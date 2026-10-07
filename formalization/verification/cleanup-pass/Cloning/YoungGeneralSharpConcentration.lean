import Cloning.YoungGeneralConcentration

/-! A stronger elementary Chernoff estimate retaining the variance of the
centered letter indicator. The spare factor in the exponential is needed to
absorb the physical Young law's polynomial dimension prefactor. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.YoungGeneral
set_option maxHeartbeats 600000

/-- Retaining the second moment improves the earlier coarse MGF constant. -/
theorem finite_mgf_half_le {d : ℕ} (p x : Fin d→ℝ)
    (hp : ∀i,0≤p i) (hs : ∑i,p i=1)
    (hx : ∀i,|x i|≤1) (hm : ∑i,p i*x i=0)
    (hv : ∑i,p i*(x i)^2≤1/2)
    (t : ℝ) (ht : |t|≤1) :
    (∑i,p i*Real.exp (t*x i))≤Real.exp (t^2/2) := by
  have hb (i : Fin d) : Real.exp (t*x i)≤1+t*x i+t^2*(x i)^2 := by
    have htx : |t*x i|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul ht (hx i) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have h := Real.norm_exp_sub_one_sub_id_le (show ‖t*x i‖≤1 by simpa using htx)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,sq_abs] at h
    have := (abs_le.mp h).2
    nlinarith
  calc
    _≤∑i,p i*(1+t*x i+t^2*(x i)^2) :=
      Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hb i) (hp i))
    _=1+t^2*∑i,p i*(x i)^2 := by
      simp_rw [mul_add,mul_one,
        show ∀i,p i*(t*x i)=t*(p i*x i) by intro i; ring,
        show ∀i,p i*(t^2*(x i)^2)=t^2*(p i*(x i)^2) by intro i; ring]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
        ← Finset.mul_sum,hs,hm]
      ring
    _≤1+t^2/2 := by nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg t)]
    _≤_ := by simpa [add_comm] using Real.add_one_le_exp (t^2/2)

theorem word_mgf_half_le {d N : ℕ} (p x : Fin d→ℝ)
    (hp : ∀i,0≤p i) (hs : ∑i,p i=1)
    (hx : ∀i,|x i|≤1) (hm : ∑i,p i*x i=0)
    (hv : ∑i,p i*(x i)^2≤1/2)
    (t : ℝ) (ht : |t|≤1) :
    (∑w : Fin N→Fin d,wordWeight p w*Real.exp (t*∑k,x (w k)))≤
      Real.exp ((N:ℝ)*t^2/2) := by
  rw [word_mgf_eq]
  calc
    _≤Real.exp (t^2/2)^N := pow_le_pow_left₀
      (Finset.sum_nonneg (fun i _=>mul_nonneg (hp i) (Real.exp_pos _).le))
      (finite_mgf_half_le p x hp hs hx hm hv t ht) N
    _=_ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem word_tail_half_le {d N : ℕ} (p x : Fin d→ℝ)
    (hp : ∀i,0≤p i) (hs : ∑i,p i=1)
    (hx : ∀i,|x i|≤1) (hm : ∑i,p i*x i=0)
    (hv : ∑i,p i*(x i)^2≤1/2)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    (∑w : Fin N→Fin d,
      if (N:ℝ)*ε≤∑k,x (w k) then wordWeight p w else 0)≤
      Real.exp (-(N:ℝ)*ε^2/2) := by
  classical
  have ht : |ε|≤1 := by simpa only [abs_of_nonneg hε] using hε1
  have hpoint (w : Fin N→Fin d) :
      (if (N:ℝ)*ε≤∑k,x (w k) then wordWeight p w else 0)≤
        Real.exp (-ε*(N:ℝ)*ε)*(wordWeight p w*Real.exp (ε*∑k,x (w k))) := by
    split_ifs with h
    · have hexp : (1:ℝ)≤Real.exp (-ε*(N:ℝ)*ε+ε*∑k,x (w k)) := by
        apply Real.one_le_exp_iff.mpr
        have := mul_le_mul_of_nonneg_left h hε
        linarith
      have hb := mul_le_mul_of_nonneg_left hexp (wordWeight_nonneg p hp w)
      rw [Real.exp_add] at hb
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (wordWeight_nonneg p hp w) (Real.exp_pos _).le)
  calc
    _≤∑w : Fin N→Fin d,Real.exp (-ε*(N:ℝ)*ε)*
        (wordWeight p w*Real.exp (ε*∑k,x (w k))) :=
      Finset.sum_le_sum (fun w _=>hpoint w)
    _=Real.exp (-ε*(N:ℝ)*ε)*
        (∑w : Fin N→Fin d,wordWeight p w*Real.exp (ε*∑k,x (w k))) :=
      (Finset.mul_sum ..).symm
    _≤Real.exp (-ε*(N:ℝ)*ε)*Real.exp ((N:ℝ)*ε^2/2) :=
      mul_le_mul_of_nonneg_left (word_mgf_half_le p x hp hs hx hm hv ε ht) (Real.exp_pos _).le
    _=_ := by rw [← Real.exp_add]; congr 1; ring

theorem centeredIndicator_secondMoment {d : ℕ} (p : Fin d→ℝ)
    (hs : ∑i,p i=1) (i : Fin d) :
    ∑j,p j*(centeredIndicator p i j)^2=p i*(1-p i) := by
  classical
  have he (j : Fin d) : p j*(centeredIndicator p i j)^2=
      (if j=i then p j else 0)-2*p i*(if j=i then p j else 0)+p j*(p i)^2 := by
    unfold centeredIndicator
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hs]
  simp
  ring

/-- A centered Bernoulli indicator has variance at most 1/4, hence at most
the 1/2 required for the stronger exponential estimate. -/
theorem centeredIndicator_secondMoment_le_half {d : ℕ} (p : Fin d→ℝ)
    (hs : ∑i,p i=1) (i : Fin d) :
    ∑j,p j*(centeredIndicator p i j)^2≤1/2 := by
  rw [centeredIndicator_secondMoment p hs i]
  nlinarith [sq_nonneg (p i-1/2)]

theorem rowCount_tail_half_le {d N : ℕ} (p : Fin d→ℝ)
    (hp : ∀i,0≤p i) (hs : ∑i,p i=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (i : Fin d) :
    (∑w : Fin N→Fin d,
      if (N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0)≤
      2*Real.exp (-(N:ℝ)*ε^2/2) := by
  classical
  let x := centeredIndicator p i
  have hp1 := word_tail_half_le (N:=N) p x hp hs
    (centeredIndicator_abs_le p hp hs i) (centeredIndicator_mean p hs i)
    (centeredIndicator_secondMoment_le_half p hs i) ε hε hε1
  have hn1 := word_tail_half_le (N:=N) p (fun j=>-x j) hp hs
    (fun j=>by simpa using centeredIndicator_abs_le p hp hs i j)
    (by simp only [mul_neg,Finset.sum_neg_distrib,centeredIndicator_mean p hs i,neg_zero,x])
    (by simpa only [neg_sq,x] using centeredIndicator_secondMoment_le_half p hs i)
    ε hε hε1
  have hpoint (w : Fin N→Fin d) :
      (if (N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0)≤
      (if (N:ℝ)*ε≤∑k,x (w k) then wordWeight p w else 0)+
      (if (N:ℝ)*ε≤∑k,-x (w k) then wordWeight p w else 0) := by
    simp only [x,centeredIndicator_sum,Finset.sum_neg_distrib]
    have hw := wordWeight_nonneg p hp w
    split_ifs <;> simp_all only [not_le,le_abs,neg_sub,false_or] <;> first | contradiction | linarith
  have hsum := Finset.sum_le_sum
    (fun w (_ : w∈(Finset.univ : Finset (Fin N→Fin d)))=>hpoint w)
  rw [Finset.sum_add_distrib] at hsum
  linarith

theorem max_rowCount_tail_half_le {d N : ℕ} (p : Fin d→ℝ)
    (hp : ∀i,0≤p i) (hs : ∑i,p i=1)
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) :
    (∑w : Fin N→Fin d,
      if ∃i,(N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0)≤
      2*d*Real.exp (-(N:ℝ)*ε^2/2) := by
  classical
  have hpoint (w : Fin N→Fin d) :
      (if ∃i,(N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0)≤
      ∑i,if (N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0 := by
    split_ifs with h
    · obtain ⟨i,hi⟩ := h
      have hh := Finset.single_le_sum (s:=(Finset.univ : Finset (Fin d)))
        (f:=fun j=>if (N:ℝ)*ε≤|(rowCount w j:ℝ)-N*p j| then wordWeight p w else 0)
        (fun j _=>by have := wordWeight_nonneg p hp w; positivity) (Finset.mem_univ i)
      simpa only [if_pos hi] using hh
    · exact Finset.sum_nonneg (fun i _=>by have := wordWeight_nonneg p hp w; positivity)
  calc
    _≤∑w : Fin N→Fin d,∑i,
        if (N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0 :=
      Finset.sum_le_sum (fun w _=>hpoint w)
    _=∑i,∑w : Fin N→Fin d,
        if (N:ℝ)*ε≤|(rowCount w i:ℝ)-N*p i| then wordWeight p w else 0 := Finset.sum_comm
    _≤∑_i : Fin d,2*Real.exp (-(N:ℝ)*ε^2/2) :=
      Finset.sum_le_sum (fun i _=>rowCount_tail_half_le p hp hs ε hε hε1 i)
    _=_ := by simp; ring

end Cloning.YoungGeneral
