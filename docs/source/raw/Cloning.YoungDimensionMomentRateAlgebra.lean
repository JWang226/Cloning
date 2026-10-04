import Cloning.YoungDimensionSecondOrder
import Cloning.YoungGeneralMoments

/-! Global second-order dimension control on the actual finite label space. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.YoungDimensionRatio
set_option maxHeartbeats 1200000

/-- A bounded finite product has a quadratic remainder, with a bound that
allows every finite physical label rather than just a central window. -/
theorem product_quadratic_remainder_bounded {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (C : ℝ) (hC : 1≤C) (hx : ∀i∈S,|1+x i|≤C) :
    |(∏i∈S,(1+x i))-1-∑i∈S,x i| ≤ C^S.card*(∑i∈S,|x i|)^2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hi := ih (fun i hi=>hx i (Finset.mem_insert_of_mem hi))
    have hxa := hx a (Finset.mem_insert_self a S)
    have hs := Finset.abs_sum_le_sum_abs (s := S) (f := x)
    have hs0 : 0≤∑i∈S,|x i| := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
    have hp : 1≤C^S.card := one_le_pow₀ hC
    have hC0 : 0≤C := zero_le_one.trans hC
    have hp0 : 0≤C^S.card := zero_le_one.trans hp
    simp only [Finset.prod_insert ha,Finset.sum_insert ha,Finset.card_insert_of_notMem ha,pow_succ]
    have he : (1+x a)*(∏i∈S,(1+x i))-1-(x a+∑i∈S,x i)=
        (1+x a)*((∏i∈S,(1+x i))-1-∑i∈S,x i)+x a*(∑i∈S,x i) := by ring
    rw [he]
    calc
      _ ≤ |1+x a| *|(∏i∈S,(1+x i))-1-∑i∈S,x i|+|x a| *|∑i∈S,x i| := by
        simpa only [abs_mul] using abs_add_le
          ((1+x a)*((∏i∈S,(1+x i))-1-∑i∈S,x i)) (x a*(∑i∈S,x i))
      _ ≤ C*(C^S.card*(∑i∈S,|x i|)^2)+|x a| *(∑i∈S,|x i|) :=
        add_le_add (mul_le_mul hxa hi (abs_nonneg _) hC0)
          (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
      _ ≤ _ := by
        have hCP : 1≤C^S.card*C := one_le_mul_of_one_le_of_one_le hp hC
        have hcross := mul_nonneg (show 0≤2*(C^S.card*C)-1 by linarith)
          (mul_nonneg (abs_nonneg (x a)) hs0)
        have hsquare := mul_nonneg (mul_nonneg hp0 hC0) (sq_nonneg |x a|)
        nlinarith

theorem product_error_le_bounded_square_sum {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (C : ℝ) (hC : 1≤C) (hx : ∀i∈S,|1+x i|≤C) :
    |(∏i∈S,(1+x i))-1| ≤ |∑i∈S,x i|+
      (C^S.card*S.card)*(∑i∈S,(x i)^2) := by
  have hr := product_quadratic_remainder_bounded S x C hC hx
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i=>|x i|) (fun _=>(1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
  have hsplit : (∏i∈S,(1+x i))-1=((∏i∈S,(1+x i))-1-∑i∈S,x i)+(∑i∈S,x i) := by ring
  rw [hsplit]
  calc
    _ ≤ |(∏i∈S,(1+x i))-1-∑i∈S,x i|+|∑i∈S,x i| := abs_add_le _ _
    _ ≤ C^S.card*(∑i∈S,|x i|)^2+|∑i∈S,x i| := add_le_add hr le_rfl
    _ ≤ C^S.card*((∑i∈S,(x i)^2)*S.card)+|∑i∈S,x i| :=
      add_le_add (mul_le_mul_of_nonneg_left hcs (pow_nonneg (zero_le_one.trans hC) _)) le_rfl
    _ = _ := by ring

private theorem bounded_second_order_envelope_le (A B C V N : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hV : 0≤V) (hN : 1≤N) :
    A/N+B*V/N^2+C/N^2≤(A+B+C)*(1/N+V/N^2) := by
  have hn : 0<N := zero_lt_one.trans_le hN
  have hNN : N≤N^2 := by nlinarith
  have hi : 1/N^2≤1/N := one_div_le_one_div_of_le hn hNN
  have hCd : C/N^2≤C/N := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi hC
  calc
    _ ≤ A/N+B*V/N^2+C/N := add_le_add le_rfl hCd
    _ = (A+C)*(1/N)+B*(V/N^2) := by ring
    _ ≤ (A+B+C)*(1/N)+(A+B+C)*(V/N^2) :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) (one_div_nonneg.mpr hn.le))
        (mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hV (sq_nonneg _)))
    _ = _ := by ring

def globalSecondOrderConstant (r k : ℕ) : ℝ :=
  (r:ℝ)*(r*k:ℕ)*((r:ℝ)+k) +
    ((1+(r:ℝ)*(1+r+k))^(r*k)*(r*k:ℕ))*2*(r:ℝ)^2*
      ((k:ℝ)+(r*k:ℕ)*((r:ℝ)+k)^2)

theorem globalSecondOrderConstant_nonneg (r k : ℕ) :
    0≤globalSecondOrderConstant r k := by unfold globalSecondOrderConstant; positivity

/-- Actual finite labels admit a global second-order bound. The only
structural hypothesis is their exact box count. -/
theorem normalizedDimension_global_second_order (r k N : ℕ) (hr : 0<r) (hN : 1≤N)
    (mu : Cloning.YoungGeneral.Shape r N) (hsum : ∑i,(mu i).val=N) :
    |Cloning.YoungGeneral.normalizedDimension r k N mu-1| ≤
      globalSecondOrderConstant r k*(1/(N:ℝ)+
        (∑i,((mu i).val-(N:ℝ)/r)^2)/(N:ℝ)^2) := by
  open Cloning.YoungGeneral in
  have hrow : ∑i,shapeRows mu i=(N:ℝ) := by
    dsimp only [shapeRows]
    exact_mod_cast hsum
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  let row := Cloning.YoungGeneral.shapeRows mu
  let C : ℝ := 1+(r:ℝ)*(1+r+k)
  let x : Fin r×Fin k→ℝ := fun a=>(r:ℝ)*(row a.1+crossingGap a)/N-1
  have hC : 1≤C := by
    dsimp [C]
    have hp : 0≤(r:ℝ)*(1+r+k) := by positivity
    linarith
  have hx1 (a : Fin r×Fin k) : 1+x a=(r:ℝ)*(row a.1+crossingGap a)/N := by dsimp [x]; ring
  have hx : ∀a∈Finset.univ,|1+x a|≤C := by
    intro a _
    have hpos : 0≤(r:ℝ)*(row a.1+crossingGap a)/N := by
      have h1 : 0≤row a.1 := Cloning.YoungGeneral.shapeRows_nonneg mu a.1
      have h2 := (crossingGap_pos a).le
      positivity
    rw [hx1,abs_of_nonneg hpos]
    have hlo := Cloning.YoungGeneral.shapeRows_le mu a.1
    have hgap := crossingGap_le a
    have hgapN := mul_le_mul_of_nonneg_left hn1
      (show (0:ℝ)≤r+k by positivity)
    apply (div_le_iff₀ hn).mpr
    dsimp only [C,row]
    have hinside : Cloning.YoungGeneral.shapeRows mu a.1+crossingGap a≤(1+(r:ℝ)+k)*N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg r)]
  have hp := product_error_le_bounded_square_sum Finset.univ x C hC hx
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hx1] at hp
  have hden : leadingConstant r k*(N:ℝ)^(r*k)≠0 :=
    (mul_pos (leadingConstant_pos r k hr) (pow_pos hn _)).ne'
  unfold Cloning.YoungGeneral.normalizedDimension
  rw [dimensionRatio_factorization r k _ N hr hn,mul_div_cancel_left₀ _ hden]
  have he := hp.trans (add_le_add (crossing_error_sum_bound r k row N hr hn hrow)
    (mul_le_mul_of_nonneg_left (crossing_error_square_sum_bound r k row N hr hn)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) (Nat.cast_nonneg _))))
  have henv := bounded_second_order_envelope_le
    ((r:ℝ)*(r*k:ℕ)*((r:ℝ)+k))
    ((C^(r*k)*(r*k:ℕ))*2*(r:ℝ)^2*k)
    ((C^(r*k)*(r*k:ℕ))*2*(r:ℝ)^2*(r*k:ℕ)*((r:ℝ)+k)^2)
    (∑i,(row i-(N:ℝ)/r)^2) N
    (by positivity) (by positivity) (by positivity)
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) hn1
  apply he.trans
  calc
    _ = (r:ℝ)*(r*k:ℕ)*((r:ℝ)+k)/(N:ℝ)+
        ((C^(r*k)*(r*k:ℕ))*2*(r:ℝ)^2*k)*(∑i,(row i-(N:ℝ)/r)^2)/(N:ℝ)^2+
        ((C^(r*k)*(r*k:ℕ))*2*(r:ℝ)^2*(r*k:ℕ)*((r:ℝ)+k)^2)/(N:ℝ)^2 := by ring
    _ ≤ _ := henv
    _ = _ := by dsimp only [globalSecondOrderConstant,C,row,Cloning.YoungGeneral.shapeRows]; ring

end Cloning.YoungDimensionRatio
