import Cloning.PhysicalFlatGrassmannEmbedding

/-! Every rectangular physical isometry is a unitary rotation of the fixed
coordinate inclusion, including its internal column basis. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Cloning.PhysicalFlatGrassmann
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The unitary extends the actual columns, not merely their range. -/
theorem exists_unitary_isometry (r k : ℕ)
    (J : Matrix (Fin (r+k)) (Fin r) ℂ) (hJ : Jᴴ*J=1) :
    ∃ W : unitary (Matrix (Fin (r+k)) (Fin (r+k)) ℂ),
      J = (W : Matrix (Fin (r+k)) (Fin (r+k)) ℂ) * coordinateInclusion r k := by
  let I := coordinateInclusion r k
  let C := coordinateProjector r k
  have hI : Iᴴ*I=1 := coordinateInclusion_isometry r k
  have hII : I*Iᴴ=C := coordinateInclusion_range r k
  have hC : C*C=C := coordinateProjector_idempotent r k
  have hCs : Cᴴ=C := (coordinateProjector_nonneg r k).isHermitian.eq
  have hP : (J*Jᴴ).IsHermitian := (Matrix.posSemidef_self_mul_conjTranspose J).isHermitian
  have hPP : (J*Jᴴ)*(J*Jᴴ)=J*Jᴴ := by
    calc
      _ = J*(Jᴴ*J)*Jᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.mul_one]
  have hrank : (J*Jᴴ).rank=r := by
    rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self J, hJ]
    simp
  obtain ⟨U,hU⟩ := exists_unitary_projector (J*Jᴴ) hP hPP hrank
  let V : Matrix (Fin (r+k)) (Fin (r+k)) ℂ := U
  have hV : Vᴴ*V=1 := Unitary.star_mul_self_of_mem U.property
  change J*Jᴴ=V*C*Vᴴ at hU
  have hCI : C*I=I := by rw [← hII, Matrix.mul_assoc, hI, Matrix.mul_one]
  have hCJ : C*Vᴴ*J=Vᴴ*J := by
    calc
      _ = Vᴴ*(V*C*Vᴴ)*J := by simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
      _ = Vᴴ*(J*Jᴴ)*J := by rw [← hU]
      _ = _ := by simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
  let Q := 1-C
  have hQs : Qᴴ=Q := by simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hCs]
  have hQQ : Q*Q=Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hC]
    abel
  have hQI : Q*I=0 := by
    change (1-C)*I=0
    rw [Matrix.sub_mul, Matrix.one_mul, hCI, sub_self]
  have hQJ : Q*Vᴴ*J=0 := by
    change (1-C)*Vᴴ*J=0
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, hCJ, sub_self]
  have hJQ : Jᴴ*V*Q=0 := by
    have h := congrArg Matrix.conjTranspose hQJ
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hQs, Matrix.conjTranspose_zero, ← Matrix.mul_assoc] using h
  let X := J*Iᴴ
  let Y := V*Q
  have hXX : Xᴴ*X=C := by
    change (J*Iᴴ)ᴴ*(J*Iᴴ)=C
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = I*(Jᴴ*J)*Iᴴ := by simp only [Matrix.mul_assoc]
      _ = C := by rw [hJ, Matrix.mul_one, hII]
  have hYY : Yᴴ*Y=Q := by
    change (V*Q)ᴴ*(V*Q)=Q
    rw [Matrix.conjTranspose_mul, hQs]
    calc
      _ = Q*(Vᴴ*V)*Q := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hV, Matrix.mul_one, hQQ]
  have hXY : Xᴴ*Y=0 := by
    change (J*Iᴴ)ᴴ*(V*Q)=0
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = I*(Jᴴ*V*Q) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hJQ, Matrix.mul_zero]
  have hYX : Yᴴ*X=0 := by
    have h := congrArg Matrix.conjTranspose hXY
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using h
  have hW : (X+Y)ᴴ*(X+Y)=1 := by
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hXX,hXY,hYX,hYY,add_zero,zero_add]
    dsimp only [Q]
    abel
  refine ⟨⟨X+Y,Matrix.mem_unitaryGroup_iff'.mpr hW⟩,?_⟩
  change J=(J*Iᴴ+V*Q)*I
  rw [Matrix.add_mul, Matrix.mul_assoc, hI, Matrix.mul_one,
    Matrix.mul_assoc, hQI, Matrix.mul_zero, add_zero]

end Cloning.PhysicalFlatGrassmann
