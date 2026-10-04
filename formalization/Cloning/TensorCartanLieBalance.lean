import Cloning.MatrixCovariantBalance

/-!
# Partial-trace balance from exact Lie intertwining

The spectator commutator vanishes under the actual finite partial trace.
An adjoint-compatible tensor-sum intertwiner therefore gives a commuting
reduced range operator; scalarity and its trace fix the dimension ratio.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
open Matrix Cloning.Compression
namespace Cloning.TensorCartanLieBalance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem partialTrace_add (X Y : Matrix (A × B) (A × B) ℂ) :
    partialTrace (X + Y) = partialTrace X + partialTrace Y := by
  ext a c
  simp [partialTrace, Finset.sum_add_distrib]

theorem partialTrace_left_tensor (G : Matrix A A ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    partialTrace ((G ⊗ₖ (1 : Matrix B B ℂ)) * X) = G * partialTrace X := by
  ext a c
  simp only [partialTrace, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

theorem partialTrace_right_tensor (G : Matrix A A ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    partialTrace (X * (G ⊗ₖ (1 : Matrix B B ℂ))) = partialTrace X * G := by
  ext a c
  simp only [partialTrace, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  simp only [mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_comm

/-- Cyclicity in the discarded factor, with no Hermitian or positivity premise. -/
theorem partialTrace_environment_cycle (G : Matrix B B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    partialTrace (((1 : Matrix A A ℂ) ⊗ₖ G) * X) =
      partialTrace (X * ((1 : Matrix A A ℂ) ⊗ₖ G)) := by
  ext a c
  simp only [partialTrace, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  exact mul_comm _ _

/-- Commutation with a tensor-sum generator descends through partial trace. -/
theorem partialTrace_tensorSum_commutes (GA : Matrix A A ℂ) (GB : Matrix B B ℂ)
    (X : Matrix (A × B) (A × B) ℂ)
    (hcomm : X * (GA ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ GB) =
      (GA ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ GB) * X) :
    partialTrace X * GA = GA * partialTrace X := by
  have h := congrArg partialTrace hcomm
  simp only [Matrix.mul_add, Matrix.add_mul, partialTrace_add,
    partialTrace_left_tensor, partialTrace_right_tensor] at h
  rw [partialTrace_environment_cycle] at h
  exact add_right_cancel h

/-- An operator and its adjoint intertwining through `V` force the range
operator `VV*` to commute; isometry is not needed for this algebraic step. -/
theorem intertwiner_range_commutes (F : Matrix (A × B) (A × B) ℂ)
    (G : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (h : F * V = V * G) (hstar : F.conjTranspose * V = V * G.conjTranspose) :
    (V * V.conjTranspose) * F = F * (V * V.conjTranspose) := by
  have hs := congrArg Matrix.conjTranspose hstar
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hs
  calc
    _ = V * (V.conjTranspose * F) := Matrix.mul_assoc _ _ _
    _ = V * (G * V.conjTranspose) := by rw [hs]
    _ = (V * G) * V.conjTranspose := (Matrix.mul_assoc _ _ _).symm
    _ = (F * V) * V.conjTranspose := by rw [h]
    _ = _ := Matrix.mul_assoc _ _ _

/-- A Lie intertwiner of adjoint-compatible generator families makes its
actual reduced range operator commute with the first family's generators. -/
theorem partialTrace_lie_intertwiner_commutes {d : ℕ}
    (GA : Fin d → Fin d → Matrix A A ℂ) (GB : Fin d → Fin d → Matrix B B ℂ)
    (GC : Fin d → Fin d → Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hGA : ∀ a b, GA b a = (GA a b).conjTranspose)
    (hGB : ∀ a b, GB b a = (GB a b).conjTranspose)
    (hGC : ∀ a b, GC b a = (GC a b).conjTranspose)
    (hintertwine : ∀ a b,
      (GA a b ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ GB a b) * V = V * GC a b)
    (a b : Fin d) :
    partialTrace (V * V.conjTranspose) * GA a b =
      GA a b * partialTrace (V * V.conjTranspose) := by
  apply partialTrace_tensorSum_commutes
  apply intertwiner_range_commutes _ (GC a b) V (hintertwine a b)
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← hGA, ← hGB, ← hGC] using hintertwine b a

/-- Scalarity fixes the balance constant by tracing the genuine isometric
range operator. The matrix dimensions are used directly. -/
theorem balanced_partialTrace_of_scalar (V : Matrix (A × B) C ℂ)
    (hA : 0 < Fintype.card A) (hV : V.conjTranspose * V = 1)
    (hscalar : ∃ c : ℂ, partialTrace (V * V.conjTranspose) = c • (1 : Matrix A A ℂ)) :
    partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  obtain ⟨c, hc⟩ := hscalar
  have htr := Cloning.MatrixCovariantBalance.trace_partialTrace_isometry V hV
  rw [hc, Matrix.trace_smul, Matrix.trace_one] at htr
  change c * (Fintype.card A : ℂ) = (Fintype.card C : ℂ) at htr
  have hcard : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hcval : c = (Fintype.card C : ℂ) / (Fintype.card A : ℂ) := (eq_div_iff hcard).mpr htr
  rw [hc, hcval]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_natCast]

/-- Exact Lie intertwining, adjoints, and first-factor commutant scalarity
imply Cartan balance. No balance or channel normalization is assumed. -/
theorem balanced_partialTrace_of_lie_intertwining {d : ℕ}
    (GA : Fin d → Fin d → Matrix A A ℂ) (GB : Fin d → Fin d → Matrix B B ℂ)
    (GC : Fin d → Fin d → Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hGA : ∀ a b, GA b a = (GA a b).conjTranspose)
    (hGB : ∀ a b, GB b a = (GB a b).conjTranspose)
    (hGC : ∀ a b, GC b a = (GC a b).conjTranspose)
    (hA : 0 < Fintype.card A) (hV : V.conjTranspose * V = 1)
    (hintertwine : ∀ a b,
      (GA a b ⊗ₖ (1 : Matrix B B ℂ) + (1 : Matrix A A ℂ) ⊗ₖ GB a b) * V = V * GC a b)
    (hscalar : ∀ M : Matrix A A ℂ, (∀ a b, M * GA a b = GA a b * M) →
      ∃ c : ℂ, M = c • (1 : Matrix A A ℂ)) :
    partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  apply balanced_partialTrace_of_scalar V hA hV
  apply hscalar
  exact partialTrace_lie_intertwiner_commutes GA GB GC V hGA hGB hGC hintertwine

end Cloning.TensorCartanLieBalance
