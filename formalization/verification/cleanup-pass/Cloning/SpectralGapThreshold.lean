import Cloning.SpectralGapCompact

/-! Sharp feasibility threshold for the compact spectral example. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace Cloning.SpectralGap
variable {d : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000

def threshold (d : ℕ) : ℝ := 2/(((d:ℝ)+1)*(d+2))

theorem threshold_pos (d : ℕ) : 0 < threshold d := by unfold threshold; positivity

theorem arithmeticVector_threshold (d : ℕ) (i : Fin (d+1)) :
    arithmeticVector d (threshold d) i = ((d:ℝ)+1-i.val)*threshold d := by
  unfold arithmeticVector threshold
  have hd : (d:ℝ)+1 ≠ 0 := by positivity
  have hd2 : (d:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

def endpointSpectrum (d : ℕ) : SimpleSpectrum (d+1) where
  eigenvalue := arithmeticVector d (threshold d)
  positive := by
    intro i
    rw [arithmeticVector_threshold]
    apply mul_pos _ (threshold_pos d)
    have hi : (i.val:ℝ) < d+1 := by exact_mod_cast i.isLt
    linarith
  strictAnti := Fin.strictAnti_iff_succ_lt.mpr fun i => by
    have h := arithmeticVector_gap d (threshold d) i
    have ht := threshold_pos d
    linarith
  normalized := arithmeticVector_sum d (threshold d)

theorem endpointSpectrum_mem (d : ℕ) : endpointSpectrum d ∈ gapSet d (threshold d) := by
  constructor
  · change threshold d ≤ arithmeticVector d (threshold d) (Fin.last d)
    rw [arithmeticVector_threshold]
    simp
  · intro i
    exact (arithmeticVector_gap d (threshold d) i).ge

theorem gapSet_coordinate_lower {κ : ℝ} (p : SimpleSpectrum (d+1))
    (hp : p∈gapSet d κ) (i : Fin (d+1)) :
    ((d:ℝ)+1-i.val)*κ ≤ p.eigenvalue i := by
  have ha : Antitone (fun i : Fin (d+1) => p.eigenvalue i+(i.val:ℝ)*κ) := by
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    have h := hp.2 j
    simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    linarith
  have h := ha (Fin.le_last i)
  have hl := hp.1
  simp only [Fin.val_last] at h hl
  nlinarith

theorem gapSet_threshold_singleton (d : ℕ) :
    gapSet d (threshold d) = {endpointSpectrum d} := by
  ext p
  constructor
  · intro hp
    have hle (i : Fin (d+1)) : (endpointSpectrum d).eigenvalue i ≤ p.eigenvalue i := by
      change arithmeticVector d (threshold d) i ≤ p.eigenvalue i
      rw [arithmeticVector_threshold]
      exact gapSet_coordinate_lower p hp i
    have he : ∀ i, (endpointSpectrum d).eigenvalue i = p.eigenvalue i := by
      have hsum : (∑ i, (endpointSpectrum d).eigenvalue i) = ∑ i, p.eigenvalue i := by
        rw [p.normalized,(endpointSpectrum d).normalized]
      exact fun i => (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).mp hsum i (Finset.mem_univ i)
    exact SimpleSpectrum.eigenvalue_injective (funext (fun i => (he i).symm))
  · rintro rfl
    exact endpointSpectrum_mem d

theorem gapSet_empty_above_threshold (d : ℕ) {κ : ℝ} (hκ : threshold d < κ) :
    gapSet d κ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hp' : p∈gapSet d (threshold d) := ⟨hκ.le.trans hp.1,fun i => hκ.le.trans (hp.2 i)⟩
  have he : p=endpointSpectrum d := by
    simpa only [gapSet_threshold_singleton,Set.mem_singleton_iff] using hp'
  subst p
  have hlast := hp.1
  change κ ≤ arithmeticVector d (threshold d) (Fin.last d) at hlast
  rw [arithmeticVector_threshold] at hlast
  simp only [Fin.val_last,add_sub_cancel_left,one_mul] at hlast
  linarith

/-- In dimensions at least two the endpoint singleton has empty interior;
it therefore fails the regular-closure hypothesis, as stated in the paper. -/
theorem gapSet_threshold_interior_empty (hd : 1≤d) :
    interior (gapSet d (threshold d)) = ∅ := by
  rw [gapSet_threshold_singleton]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have he : p=endpointSpectrum d := Set.mem_singleton_iff.mp (interior_subset hp)
  subst p
  have hκ := threshold_pos d
  let q := arithmeticSpectrum d (threshold d/2) (by positivity) (by
    change threshold d/2 < threshold d
    linarith)
  have hlast : (endpointSpectrum d).eigenvalue (Fin.last d) = threshold d := by
    change arithmeticVector d (threshold d) (Fin.last d) = _
    rw [arithmeticVector_threshold]
    simp
  have hq : (endpointSpectrum d).eigenvalue (Fin.last d) < q.eigenvalue (Fin.last d) := by
    have hd' : (0:ℝ)<d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
    have hprod := mul_pos hd' hκ
    have heq := hlast
    change 1/((d:ℝ)+1)+((d:ℝ)/2-d)*threshold d = threshold d at heq
    change (endpointSpectrum d).eigenvalue (Fin.last d) <
      1/((d:ℝ)+1)+((d:ℝ)/2-d)*(threshold d/2)
    rw [hlast]
    nlinarith
  have ht (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity
  have ht1 (n : ℕ) : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith)
  let u (n : ℕ) := mix (endpointSpectrum d) q (1/((n:ℝ)+1)) (ht n).le (ht1 n)
  have hc : Tendsto u atTop (𝓝 (endpointSpectrum d)) := by
    apply SimpleSpectrum.isEmbedding_eigenvalue.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [u,mix] using (((tendsto_const_nhds (x := (1:ℝ))).sub hz).mul_const
      ((endpointSpectrum d).eigenvalue i)).add (hz.mul_const (q.eigenvalue i))
  obtain ⟨n,hn⟩ := (hc.eventually (isOpen_interior.mem_nhds hp)).exists
  have hu : u n = endpointSpectrum d := Set.mem_singleton_iff.mp (interior_subset hn)
  have hcoord := congrArg (fun p : SimpleSpectrum (d+1) => p.eigenvalue (Fin.last d)) hu
  change (1-1/((n:ℝ)+1))*(endpointSpectrum d).eigenvalue (Fin.last d)+
    (1/((n:ℝ)+1))*q.eigenvalue (Fin.last d) = (endpointSpectrum d).eigenvalue (Fin.last d) at hcoord
  nlinarith [mul_pos (ht n) (sub_pos.mpr hq)]

theorem gapSet_threshold_not_regular (hd : 1≤d) :
    closure (interior (SimpleSpectrum.toAffine '' gapSet d (threshold d))) ≠
      SimpleSpectrum.toAffine '' gapSet d (threshold d) := by
  intro h
  have hreg := SimpleSpectrum.regularClosure_of_affine _ h
  rw [gapSet_threshold_interior_empty hd,closure_empty] at hreg
  have hp := endpointSpectrum_mem d
  rw [← hreg] at hp
  exact hp

theorem gapSet_minimax_tendsto (hd : 1≤d) {κ : ℝ} (hκ : 0<κ)
    (hupper : κ<threshold d) (m : ℕ→ℕ) (γ : ℝ) (hγ : 1<γ)
    (hgain : Tendsto (fun n => (m n:ℝ)/n) atTop (𝓝 γ)) :
    Tendsto (fun n => TensorCloning.unknownSpectrumValue n (m n) (gapSet d κ)) atTop
      (𝓝 (⨅ p : gapSet d κ, universalValue γ p.val)) := by
  obtain ⟨hc,hne,hr⟩ := gapSet_hypotheses d hκ hupper
  exact TensorCloning.unknownSpectrumValue_tendsto_affine hd _ hc hne hr m γ hγ hgain

end Cloning.SpectralGap
