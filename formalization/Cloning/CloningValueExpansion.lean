import Cloning.CloningValueExpansionClassical

/-! The manuscript's fixed-spectrum high-fidelity expansions, with cubic errors. -/
noncomputable section
open scoped Topology BigOperators
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def knownCoefficient {d : ℕ} (p : SimpleSpectrum d) : ℝ :=
  ∑ij : PairIndex d,1/(4*p.ratio ij)

def universalCoefficient {d : ℕ} (p : SimpleSpectrum d) : ℝ :=
  ((d:ℝ)-1)/8+knownCoefficient p

def pctCoefficient {d : ℕ} (p : SimpleSpectrum d) : ℝ :=
  ((d:ℝ)-1)/2+∑ij : PairIndex d,(1+p.ratio ij)^2/(4*p.ratio ij)

theorem knownCoefficient_eq {d : ℕ} (p : SimpleSpectrum d) :
    knownCoefficient p=(1/4)*∑ij : PairIndex d,p.eigenvalue ij.val.1/p.eigenvalue ij.val.2 := by
  rw [knownCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  dsimp only [SimpleSpectrum.ratio]
  field_simp [(p.positive ij.val.1).ne',(p.positive ij.val.2).ne']

theorem universalCoefficient_eq {d : ℕ} (p : SimpleSpectrum d) :
    universalCoefficient p=((d:ℝ)-1)/8+
      (1/4)*∑ij : PairIndex d,p.eigenvalue ij.val.1/p.eigenvalue ij.val.2 := by
  rw [universalCoefficient,knownCoefficient_eq]

theorem pctCoefficient_eq {d : ℕ} (p : SimpleSpectrum d) :
    pctCoefficient p=((d:ℝ)-1)/2+
      (1/4)*∑ij : PairIndex d,(p.eigenvalue ij.val.1+p.eigenvalue ij.val.2)^2/
        (p.eigenvalue ij.val.1*p.eigenvalue ij.val.2) := by
  rw [pctCoefficient,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  dsimp only [SimpleSpectrum.ratio]
  field_simp [(p.positive ij.val.1).ne',(p.positive ij.val.2).ne']
  <;> ring

theorem orbital_squared_remainder {d : ℕ} (p : SimpleSpectrum d) :
    (fun x=>orbitalValue (1+x) p^2-(1-knownCoefficient p*x^2))
      =O[𝓝[>] (0:ℝ)] (fun x=>x^3) := by
  have h := HasQuadraticExpansion.prod Finset.univ
    (fun ij : PairIndex d=>fun x=>Thermal.fidelity (p.ratio ij)
      (Thermal.amplified (1+x) (p.ratio ij))^2)
    (fun ij=>1/(4*p.ratio ij))
    (fun ij _=>amplified_fidelity_expansion (p.ratio_pos ij) (p.ratio_lt_one ij))
  have hh := h.mono (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  apply hh.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [HasQuadraticExpansion,knownCoefficient,orbitalValue]
  have he (ij : PairIndex d) : Thermal.fidelity (p.ratio ij)
      (Thermal.amplified (1+x) (p.ratio ij))=Thermal.modeFactor (1+x) (p.ratio ij) :=
    Thermal.fidelity_amplified_eq_modeFactor (by change 0<x at hx; linarith)
      (p.ratio_pos ij).le (p.ratio_lt_one ij)
  simp_rw [he]
  rw [Finset.prod_pow]

theorem universal_squared_remainder {d : ℕ} (p : SimpleSpectrum d) :
    (fun x=>universalValue (1+x) p^2-(1-universalCoefficient p*x^2))
      =O[𝓝[>] (0:ℝ)] (fun x=>x^3) := by
  have hprod := HasQuadraticExpansion.prod Finset.univ
    (fun ij : PairIndex d=>fun x=>Thermal.fidelity (p.ratio ij)
      (Thermal.amplified (1+x) (p.ratio ij))^2)
    (fun ij=>1/(4*p.ratio ij))
    (fun ij _=>amplified_fidelity_expansion (p.ratio_pos ij) (p.ratio_lt_one ij))
  have hc : HasQuadraticExpansion (fun x=>classicalValue (1+x) d^2) (((d:ℝ)-1)/8) := by
    simpa using classicalValue_squared_expansion 1 d
  have hh := (hc.mul hprod).mono (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  apply hh.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [HasQuadraticExpansion,universalCoefficient,knownCoefficient,universalValue,orbitalValue]
  have he (ij : PairIndex d) : Thermal.fidelity (p.ratio ij)
      (Thermal.amplified (1+x) (p.ratio ij))=Thermal.modeFactor (1+x) (p.ratio ij) :=
    Thermal.fidelity_amplified_eq_modeFactor (by change 0<x at hx; linarith)
      (p.ratio_pos ij).le (p.ratio_lt_one ij)
  simp_rw [he]
  rw [Finset.prod_pow,mul_pow]

theorem pct_squared_remainder {d : ℕ} (p : SimpleSpectrum d) :
    (fun x=>pctValue (1+x) p^2-(1-pctCoefficient p*x^2))
      =O[𝓝 (0:ℝ)] (fun x=>x^3) := by
  have hprod := HasQuadraticExpansion.prod Finset.univ
    (fun ij : PairIndex d=>fun x=>Thermal.fidelity (p.ratio ij)
      (Thermal.pct (1+x) (p.ratio ij))^2)
    (fun ij=>(1+p.ratio ij)^2/(4*p.ratio ij))
    (fun ij _=>pct_fidelity_expansion (p.ratio_pos ij) (p.ratio_lt_one ij))
  have hc : HasQuadraticExpansion (fun x=>classicalValue (1+2*x) d^2) (((d:ℝ)-1)/2) := by
    convert classicalValue_squared_expansion 2 d using 1
    ring
  have hh := hc.mul hprod
  dsimp only [HasQuadraticExpansion] at hh
  convert hh using 1
  ext x
  dsimp only [HasQuadraticExpansion,pctCoefficient,pctValue]
  rw [show 2*(1+x)-1=1+2*x by ring,Finset.prod_pow,mul_pow]

theorem universalCoefficient_lt_pctCoefficient {d : ℕ} (hd : 2≤d)
    (p : SimpleSpectrum d) : universalCoefficient p<pctCoefficient p := by
  have hs : knownCoefficient p≤∑ij : PairIndex d,(1+p.ratio ij)^2/(4*p.ratio ij) := by
    apply Finset.sum_le_sum
    intro ij _
    apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) (p.ratio_pos ij).le)
    nlinarith [p.ratio_pos ij,sq_nonneg (p.ratio ij)]
  have hd' : (2:ℝ)≤d := by exact_mod_cast hd
  dsimp only [universalCoefficient,pctCoefficient]
  linarith

end Cloning.ValueExpansion
