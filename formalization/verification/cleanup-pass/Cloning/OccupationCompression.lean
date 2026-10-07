import Cloning.SymmetricOccupation

/-! Explicit rectangular occupation-compression Kraus operators. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter
namespace Cloning.SymmetricOccupation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

abbrev Fock := lp (fun _ : ℕ => ℂ) 2

def restrictCLM (L : ℕ) : Fock →L[ℂ] OccupationSpace L :=
  LinearMap.mkContinuous
    { toFun := restrict L
      map_add' := by intro x y; ext j; rfl
      map_smul' := by intro c x; ext j; rfl }
    1 (by intro x; simpa using restrict_norm_le L x)

def compression (L : ℕ) : Fock →L[ℂ] TensorSpace L :=
  (isometry L).toContinuousLinearMap.comp (restrictCLM L)

@[simp] theorem compression_apply (L : ℕ) (x : Fock) :
    compression L x = isometry L (restrict L x) := rfl

def coordinate (j : ℕ) : Fock →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x j
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
    1 (by intro x; simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x j)

def tailKraus (L j : ℕ) : Fock →L[ℂ] TensorSpace L :=
  if L < j then (ContinuousLinearMap.toSpanSingleton ℂ (column L 0)).comp (coordinate j) else 0

@[simp] theorem tailKraus_apply (L j : ℕ) (x : Fock) :
    tailKraus L j x = if L < j then x j • column L 0 else 0 := by
  unfold tailKraus
  split_ifs <;> rfl

theorem tailKraus_norm_sq (L j : ℕ) (x : Fock) :
    ‖tailKraus L j x‖ ^ 2 = if L < j then ‖x j‖ ^ 2 else 0 := by
  rw [tailKraus_apply]
  split_ifs <;> simp [norm_smul, column_norm]

theorem restrict_norm_sq (L : ℕ) (x : Fock) :
    ‖restrict L x‖ ^ 2 = ∑ j ∈ Finset.range (L + 1), ‖x j‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (restrict L x)
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype, restrict_apply] using h

theorem tailKraus_norm_sq_hasSum (L : ℕ) (x : Fock) :
    HasSum (fun j => ‖tailKraus L j x‖ ^ 2) (‖x‖ ^ 2 - ‖restrict L x‖ ^ 2) := by
  have hall : HasSum (fun j : ℕ => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (show 0 < (2 : ENNReal).toReal by norm_num) x
  have hhead : HasSum (fun j : ℕ => if j ≤ L then ‖x j‖ ^ 2 else 0) (‖restrict L x‖ ^ 2) := by
    rw [restrict_norm_sq]
    have hs : HasSum (fun j : ℕ => if j ≤ L then ‖x j‖ ^ 2 else 0)
        (∑ j ∈ Finset.range (L + 1), if j ≤ L then ‖x j‖ ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero
      (s := Finset.range (L + 1))
      (f := fun j : ℕ => if j ≤ L then ‖x j‖ ^ 2 else 0)
      (by intro j hj; simp only [Finset.mem_range] at hj; simp [show ¬ j ≤ L by omega])
    convert hs using 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp [show j ≤ L by omega]
  convert hall.sub hhead using 1
  ext j
  rw [tailKraus_norm_sq]
  split_ifs <;> simp_all <;> omega

/-- The retained coherent block, followed by one vacuum-replacement operator
for each discarded occupation. -/
def occupationKraus (L : ℕ) : ℕ → Fock →L[ℂ] TensorSpace L
  | 0 => compression L
  | j + 1 => tailKraus L j

theorem occupationKraus_norm_sq_hasSum (L : ℕ) (x : Fock) :
    HasSum (fun j => ‖occupationKraus L j x‖ ^ 2) (‖x‖ ^ 2) := by
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [occupationKraus, Finset.sum_range_one, compression_apply,
    LinearIsometry.norm_map] using tailKraus_norm_sq_hasSum L x

end Cloning.SymmetricOccupation
