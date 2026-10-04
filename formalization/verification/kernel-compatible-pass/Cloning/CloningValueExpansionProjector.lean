import Cloning.CloningValueExpansionClassical

/-! The additional projector-PCT classical factor has a second-order gap
with the exact cubic remainder stated in the manuscript. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace Cloning.ValueExpansion
set_option backward.isDefEq.respectTransparency false

theorem projector_pct_factor_remainder (r : ℕ) (hr : 1≤r) :
    (fun x : ℝ=>(Real.sqrt (1+2*x)/(1+x))^(r-1)-(1-((r:ℝ)-1)/2*x^2))
      =O[𝓝 (0:ℝ)] (fun x=>x^3) := by
  have h := classicalValue_squared_expansion 2 r
  have he : ∀ᶠx : ℝ in 𝓝 0,0<1+2*x :=
    (show ContinuousAt (fun x : ℝ=>1+2*x) 0 by fun_prop)
      (Ioi_mem_nhds (by norm_num))
  apply h.congr' ?_ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [he] with x hx
  have hb := (Thermal.classicalBase_pos hx).le
  have hbase : Thermal.classicalBase (1+2*x)=Real.sqrt (1+2*x)/(1+x) := by
    dsimp only [Thermal.classicalBase]
    have hden : 1+x≠0 := by linarith
    field_simp [hden]
    <;> ring
  dsimp only [HasQuadraticExpansion,classicalValue]
  have hcast : (r:ℝ)-1=((r-1:ℕ):ℝ) := by rw [Nat.cast_sub hr,Nat.cast_one]
  rw [←Real.rpow_mul_natCast hb,show (((r:ℝ)-1)/2)*(2:ℕ)=((r:ℝ)-1) by push_cast; ring,
    hcast,Real.rpow_natCast,hbase]
  congr 1
  ring

end Cloning.ValueExpansion
