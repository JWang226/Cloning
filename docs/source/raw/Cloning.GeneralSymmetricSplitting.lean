import Cloning.GeneralSymmetricDimension
import Cloning.GeneralCoherentMultiplicity
import Cloning.CartanChannel

/-! # The actual arbitrary-dimensional symmetric-tensor splitting matrix

Occupation profiles add under concatenation of computational tensors. The
Cartan inclusion of the `(n+r)`-particle symmetric sector in the product of
the two symmetric sectors is constructed from its exact normalized fiber
coefficients and identified with the literal computational tensor inclusion.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix Kronecker

namespace Cloning.GeneralSymmetricOccupation

/-- Concatenation of computational words. -/
def wordPairEquiv (n r d : ℕ) : Word n d × Word r d ≃ Word (n + r) d where
  toFun p := Fin.append p.1 p.2
  invFun w := (fun i => w (Fin.castAdd r i), fun j => w (Fin.natAdd n j))
  left_inv p := by ext i <;> simp
  right_inv w := Fin.append_castAdd_natAdd

private theorem profile_eq_sum {L d : ℕ} (w : Word L d) (a : Fin d) :
    profile w a = ∑ i : Fin L, if w i = a then 1 else 0 := by
  classical
  simp only [profile, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem profile_append {n r d : ℕ} (w : Word n d) (z : Word r d) :
    profile (Fin.append w z) = profile w + profile z := by
  classical
  funext a
  rw [profile_eq_sum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply, ← profile_eq_sum]

/-- The summed occupation profile of two tensor factors. -/
def merge {n r d : ℕ} (p : Occupation n d) (q : Occupation r d) : Occupation (n + r) d :=
  (compositionEquiv (n + r) d).symm
    ⟨p.val + q.val, by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) (compositionEquiv n d p).property
        (compositionEquiv r d q).property⟩

@[simp] theorem merge_val {n r d : ℕ} (p : Occupation n d) (q : Occupation r d) :
    (merge p q).val = p.val + q.val := rfl

@[simp] theorem merge_label {n r d : ℕ} (w : Word n d) (z : Word r d) :
    merge (label w) (label z) = label (Fin.append w z) :=
  Subtype.ext (profile_append w z).symm

theorem merge_left_injective {n r d : ℕ} (q : Occupation r d) :
    Function.Injective (fun p : Occupation n d => merge p q) := by
  intro p t h
  apply Subtype.ext
  funext a
  have he := congrArg (fun u : Occupation (n + r) d => u.val a) h
  change p.val a + q.val a = t.val a + q.val a at he
  omega

/-- The computational-basis matrix of the previously constructed occupation isometry. -/
def columnMatrix (L d : ℕ) : Matrix (Word L d) (Occupation L d) ℂ :=
  fun w q => column q w

theorem columnMatrix_isometry (L d : ℕ) :
    (columnMatrix L d).conjTranspose * columnMatrix L d = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, columnMatrix]
  have hi := orthonormal_iff_ite.mp (column_orthonormal L d) p q
  rw [lp.inner_eq_tsum, tsum_fintype] at hi
  simpa only [RCLike.inner_apply, starRingEnd_apply, mul_comm, Matrix.one_apply] using hi

/-- Exact symmetric splitting amplitudes, with their computational multiplicities. -/
def splittingMatrix (n r d : ℕ) :
    Matrix (Occupation n d × Occupation r d) (Occupation (n + r) d) ℂ :=
  fun p t => if t = merge p.1 p.2 then
    (Real.sqrt (multiplicity p.1 : ℝ) : ℂ) * (Real.sqrt (multiplicity p.2 : ℝ) : ℂ) /
      (Real.sqrt (multiplicity t : ℝ) : ℂ) else 0

/-- The output occupation inclusion, expressed in the concatenated computational basis. -/
def splitColumnMatrix (n r d : ℕ) :
    Matrix (Word n d × Word r d) (Occupation (n + r) d) ℂ :=
  fun w t => column t (wordPairEquiv n r d w)

/-- Exact physical identification of the Cartan inclusion: its coefficients
are derived from the actual normalized computational occupation fibers. -/
theorem splittingMatrix_physical (n r d : ℕ) :
    (columnMatrix n d ⊗ₖ columnMatrix r d) * splittingMatrix n r d =
      splitColumnMatrix n r d := by
  classical
  ext ⟨w, z⟩ t
  simp only [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    columnMatrix, column_apply]
  rw [Finset.sum_eq_single (label w)]
  · rw [Finset.sum_eq_single (label z)]
    · simp only [splittingMatrix, splitColumnMatrix, wordPairEquiv, Equiv.coe_fn_mk, column_apply, ite_true]
      rw [← merge_label]
      by_cases ht : t = merge (label w) (label z)
      · rw [if_pos ht, if_pos ht.symm]
        have hp : (Real.sqrt (multiplicity (label w) : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos (label w))).ne'
        have hq : (Real.sqrt (multiplicity (label z) : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos (label z))).ne'
        field_simp
      · rw [if_neg ht, if_neg (Ne.symm ht)]
        simp
    · intro q hq hn
      simp [Ne.symm hn]
    · simp
  · intro p hp hn
    simp [Ne.symm hn]
  · simp

theorem splitColumnMatrix_isometry (n r d : ℕ) :
    (splitColumnMatrix n r d).conjTranspose * splitColumnMatrix n r d = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, splitColumnMatrix]
  rw [(wordPairEquiv n r d).sum_comp (fun w => star (column p w) * column q w)]
  exact congrArg (fun M : Matrix (Occupation (n + r) d) (Occupation (n + r) d) ℂ => M p q)
    (columnMatrix_isometry (n + r) d)

/-- The constructed symmetric splitting matrix is an isometry. -/
theorem splittingMatrix_isometry (n r d : ℕ) :
    (splittingMatrix n r d).conjTranspose * splittingMatrix n r d = 1 := by
  have h := splitColumnMatrix_isometry n r d
  rw [← splittingMatrix_physical, Matrix.conjTranspose_mul] at h
  have hT : (columnMatrix n d ⊗ₖ columnMatrix r d).conjTranspose *
      (columnMatrix n d ⊗ₖ columnMatrix r d) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      columnMatrix_isometry, columnMatrix_isometry, Matrix.one_kronecker_one]
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc (columnMatrix n d ⊗ₖ columnMatrix r d).conjTranspose,
    hT, Matrix.one_mul] using h

end Cloning.GeneralSymmetricOccupation
