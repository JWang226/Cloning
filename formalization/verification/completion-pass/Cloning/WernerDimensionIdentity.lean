import Cloning.WernerNormalization

/-! The exact symmetric-dimension normalization converting the physical
Werner compression eigenvalue into the occupation law. -/
namespace Cloning.Occupation

theorem werner_dimension_identity (n m s z : ℕ) (hnm : n ≤ m) :
    ((n + s).choose s : ℝ) / ((m + s).choose s : ℝ) *
      ((z.choose n : ℝ) / (m.choose n : ℝ)) =
        (z.choose n : ℝ) / ((m + s).choose (n + s) : ℝ) := by
  have ha : ((m + s).choose s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left s m)).ne'
  have hb : (m.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hnm).ne'
  have hc : ((m + s).choose (n + s) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.add_le_add_right hnm s)).ne'
  have hid : ((m + s).choose (n + s) : ℝ) * ((n + s).choose s : ℝ) =
      ((m + s).choose s : ℝ) * (m.choose n : ℝ) := by
    exact_mod_cast (by simpa using
      (Nat.choose_mul (n := m + s) (k := n + s) (s := s) (Nat.le_add_left s n)))
  field_simp
  nlinarith [congrArg (fun x : ℝ => (z.choose n : ℝ) * x) hid]

end Cloning.Occupation
