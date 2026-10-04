import Cloning.TensorFlatProjectorMatrix
import Cloning.TensorCartanChannel

/-! Exact flat-target fidelity from physical support-projection covariance. -/
noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace Cloning.TensorLie
open Cloning.MatrixFidelity
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

section Matrices
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- Flat-target fidelity depends only on the exact target-support compression. -/
theorem fidelity_of_projector_compression (X P : Matrix C C ℂ) (c q : ℝ)
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hP : P.PosSemidef) (hPP : P*P=P)
    (hXP : P*X*P=c • P) :
    fidelity X (q • P) = Real.sqrt (c*q) * (Matrix.trace P).re := by
  unfold fidelity
  rw [sqrt_smul_projector hP hPP q hq]
  have hs : (Real.sqrt q • P)*X*(Real.sqrt q • P)=(c*q) • P := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hXP, smul_smul, Real.mul_self_sqrt hq]
    congr 1
    ring
  rw [hs, sqrt_smul_projector hP hPP (c*q) (mul_nonneg hc hq)]
  simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- Covariance at a support projection determines the entire compressed
Cartan output, with no smaller-rank intertwiner premise. -/
theorem cartan_support_compression (V : Matrix (A×B) C ℂ)
    (Pa : Matrix A A ℂ) (Pb : Matrix B B ℂ) (Pc : Matrix C C ℂ)
    (hV : Vᴴ*V=1) (hPa : Pa*Pa=Pa) (hPc : Pc*Pc=Pc)
    (hcov : V*Pc=(Pa⊗ₖPb)*V) :
    Pc*(Vᴴ*(Pa⊗ₖ(1 : Matrix B B ℂ))*V)*Pc=Pc := by
  have hprod : (Pa⊗ₖ(1 : Matrix B B ℂ))*(Pa⊗ₖPb)=Pa⊗ₖPb := by
    rw [← Matrix.mul_kronecker_mul, hPa, Matrix.one_mul]
  have hvp : (Pa⊗ₖ(1 : Matrix B B ℂ))*(V*Pc)=V*Pc := by
    rw [hcov, ← Matrix.mul_assoc, hprod]
  calc
    _ = Pc*(Vᴴ*((Pa⊗ₖ(1 : Matrix B B ℂ))*(V*Pc))) := by simp only [Matrix.mul_assoc]
    _ = Pc*(Vᴴ*(V*Pc)) := by rw [hvp]
    _ = Pc*((Vᴴ*V)*Pc) := by simp only [Matrix.mul_assoc]
    _ = Pc := by rw [hV, Matrix.one_mul, hPc]

/-- Exact sector fidelity for the genuine Cartan compression formula. -/
theorem sectorMap_flat_projector_fidelity (V : Matrix (A×B) C ℂ)
    (Pa : Matrix A A ℂ) (Pb : Matrix B B ℂ) (Pc : Matrix C C ℂ)
    (Da Dc sa sc : ℝ) (hDa : 0 < Da) (hDc : 0 < Dc) (hsa : 0 < sa) (hsc : 0 < sc)
    (hV : Vᴴ*V=1) (hPa : Pa*Pa=Pa) (hPc : Pc*Pc=Pc) (hPcpos : Pc.PosSemidef)
    (htrace : (Matrix.trace Pc).re=sc) (hcov : V*Pc=(Pa⊗ₖPb)*V) :
    fidelity (Cloning.Compression.sectorMap Da Dc V ((1/sa) • Pa)) ((1/sc) • Pc) =
      Real.sqrt ((Da/Dc)*(sc/sa)) := by
  have hcomp : Pc*Cloning.Compression.sectorMap Da Dc V ((1/sa) • Pa)*Pc =
      ((Da/Dc)*(1/sa)) • Pc := by
    unfold Cloning.Compression.sectorMap
    simp only [Matrix.smul_kronecker, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [cartan_support_compression V Pa Pb Pc hV hPa hPc hcov]
  rw [fidelity_of_projector_compression _ Pc ((Da/Dc)*(1/sa)) (1/sc)
    (by positivity) (by positivity) hPcpos hPc hcomp, htrace]
  calc
    _ = Real.sqrt (((Da/Dc)*(1/sa))*(1/sc))*Real.sqrt (sc^2) := by rw [Real.sqrt_sq hsc.le]
    _ = Real.sqrt ((((Da/Dc)*(1/sa))*(1/sc))*sc^2) :=
      (Real.sqrt_mul (by positivity) _).symm
    _ = _ := by
      congr 1
      field_simp

end Matrices

end Cloning.TensorLie
