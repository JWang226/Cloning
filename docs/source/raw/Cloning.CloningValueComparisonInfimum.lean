import Cloning.CloningValueComparisonGeometric

/-! The exact scalar infimum over simple spectra, witnessed by actual geometric spectra. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cloning.ValueComparison
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem modeFactor_zero {g : ℝ} (hg : 0<g) :
    Thermal.modeFactor g 0=(Real.sqrt g)⁻¹ := by
  simp only [Thermal.modeFactor,zero_mul,Real.sqrt_zero,add_zero]
  have hs : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  apply (mul_eq_one_iff_eq_inv₀ hs).mp
  rw [div_mul_eq_mul_div,←pow_two,Real.sq_sqrt hg.le,div_self hg.ne']

theorem modeFactor_ge_zero {g q : ℝ} (hg : 1<g) (hq : 0≤q) :
    (Real.sqrt g)⁻¹ ≤ Thermal.modeFactor g q := by
  rw [←modeFactor_zero (by linarith : 0<g)]
  exact (modeFactor_strictMonoOn hg).monotoneOn (by norm_num : (0:ℝ) ∈ Set.Ici 0) hq hq

theorem orbitalValue_ge_zero_power {d : ℕ} {g : ℝ} (hg : 1<g) (p : SimpleSpectrum d) :
    ((Real.sqrt g)⁻¹)^Fintype.card (PairIndex d) ≤ orbitalValue g p := by
  simpa only [Finset.prod_const,Finset.card_univ] using
    (Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _ : PairIndex d => (Real.sqrt g)⁻¹)
      (g:=fun ij => Thermal.modeFactor g (p.ratio ij))
      (fun _ _ => by positivity) (fun ij _ => modeFactor_ge_zero hg (p.ratio_pos ij).le))

theorem universalValue_ge_zero_power {d : ℕ} {g : ℝ} (hg : 1<g) (p : SimpleSpectrum d) :
    classicalValue g d*((Real.sqrt g)⁻¹)^Fintype.card (PairIndex d) ≤ universalValue g p :=
  mul_le_mul_of_nonneg_left (orbitalValue_ge_zero_power hg p)
    (classicalValue_pos (by linarith) d).le

theorem geometricSequence_orbital_tendsto (d : ℕ) (hd : 1≤d) {g : ℝ} (hg : 1<g) :
    Tendsto (fun n => orbitalValue g (geometricSequence d hd n)) atTop
      (𝓝 (((Real.sqrt g)⁻¹)^Fintype.card (PairIndex d))) := by
  have hc : ContinuousAt (Thermal.modeFactor g) 0 :=
    (Thermal.modeFactor_continuousAt (g:=g) (q:=0) (by linarith)).comp
      (by fun_prop : ContinuousAt (fun x : ℝ => (g,x)) 0)
  have ht (ij : PairIndex d) := hc.tendsto.comp (geometricSequence_ratio_tendsto d hd ij)
  have h := tendsto_finset_prod Finset.univ (fun ij _ => ht ij)
  simpa only [orbitalValue,modeFactor_zero (by linarith : 0<g),
    Finset.prod_const,Finset.card_univ] using h

theorem geometricSequence_universal_tendsto (d : ℕ) (hd : 1≤d) {g : ℝ} (hg : 1<g) :
    Tendsto (fun n => universalValue g (geometricSequence d hd n)) atTop
      (𝓝 (classicalValue g d*((Real.sqrt g)⁻¹)^Fintype.card (PairIndex d))) :=
  (geometricSequence_orbital_tendsto d hd hg).const_mul (classicalValue g d)

theorem zero_power_eq_rpow (d : ℕ) (hd : 1≤d) {g : ℝ} (hg : 0<g) :
    ((Real.sqrt g)⁻¹)^Fintype.card (PairIndex d)=g^(-((d:ℝ)*((d:ℝ)-1))/4) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg hg.le,←Real.rpow_natCast,
    ←Real.rpow_mul hg.le,pairIndex_card_real d hd]
  congr 1
  ring

theorem universalValue_ge_infimum {d : ℕ} (hd : 1≤d) {g : ℝ} (hg : 1<g)
    (p : SimpleSpectrum d) :
    classicalValue g d*g^(-((d:ℝ)*((d:ℝ)-1))/4) ≤ universalValue g p := by
  simpa only [zero_power_eq_rpow d hd (by linarith : 0<g)] using
    universalValue_ge_zero_power hg p

/-- The exact infimum in the all-state upper bound, including physical dimension one. -/
theorem universalValue_iInf (d : ℕ) (hd : 1≤d) {g : ℝ} (hg : 1<g) :
    (⨅p : SimpleSpectrum d, universalValue g p)=
      classicalValue g d*g^(-((d:ℝ)*((d:ℝ)-1))/4) := by
  letI : Nonempty (SimpleSpectrum d) := ⟨geometricSequence d hd 0⟩
  have hb : BddBelow (Set.range (universalValue g : SimpleSpectrum d→ℝ)) :=
    ⟨0,by rintro _ ⟨p,rfl⟩; exact (universalValue_pos hg p).le⟩
  apply le_antisymm
  · have h := ge_of_tendsto (geometricSequence_universal_tendsto d hd hg)
      (Filter.Eventually.of_forall (fun n => ciInf_le hb (geometricSequence d hd n)))
    simpa only [zero_power_eq_rpow d hd (by linarith : 0<g)] using h
  · exact le_ciInf (fun p => universalValue_ge_infimum hd hg p)

end Cloning.ValueComparison
