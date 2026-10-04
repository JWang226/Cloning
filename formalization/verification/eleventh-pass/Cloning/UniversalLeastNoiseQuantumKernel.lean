import Cloning.UniversalLeastNoiseKernel
import Cloning.WeylQuantumPositiveBounds

/-! The quantum-positive Weyl kernel is a normalized positive kernel on the
actual phase space. Finite positivity is transported from numbered tests to
arbitrary finite subsets without any representation theorem. -/

noncomputable section
open scoped ComplexOrder InnerProductSpace BigOperators

namespace Cloning.MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ} {f : (Fin d → ℂ) → ℂ} {r : ℝ}

/-- Numbered quantum positivity tests also cover every finite index type. -/
theorem IsQuantumPositive.finite_test (hf : IsQuantumPositive f r)
    {ι : Type*} [Fintype ι] (b : ι → (Fin d → ℂ)) (c : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, star (c i) * c j * quantumPositiveKernel f r (b i) (b j) := by
  let e := (Fintype.equivFin ι).symm
  have h := hf (Fintype.card ι) (fun i => b (e i)) (fun i => c (e i))
  have hsum : (∑ i : Fin (Fintype.card ι), ∑ j : Fin (Fintype.card ι),
      star (c (e i)) * c (e j) * quantumPositiveKernel f r (b (e i)) (b (e j))) =
      ∑ i : ι, ∑ j : ι, star (c i) * c j * quantumPositiveKernel f r (b i) (b j) := by
    calc
      _ = ∑ i : Fin (Fintype.card ι), ∑ j : ι,
          star (c (e i)) * c j * quantumPositiveKernel f r (b (e i)) (b j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => star (c (e i)) * c j *
          quantumPositiveKernel f r (b (e i)) (b j))
      _ = _ := e.sum_comp (fun i => ∑ j : ι,
          star (c i) * c j * quantumPositiveKernel f r (b i) (b j))
  rwa [hsum] at h

/-- The scalar Weyl kernel has exactly the normalization, symmetry, and
finite-subset positivity needed by the Hilbert-space kernel construction. -/
theorem IsQuantumPositive.normalizedPositiveKernel
    (hf : IsQuantumPositive f r) (hf0 : f 0 = 1) :
    Cloning.PositiveKernel.IsNormalizedPositive (quantumPositiveKernel f r) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change (starRingEnd ℂ) (quantumPositiveKernel f r y x) = _
    simp only [quantumPositiveKernel, map_mul, map_div₀,
      ← displacementPhase_neg_swap, neg_neg]
    rw [starRingEnd_apply, ← hf.conj_symm hf0]
    congr 2
    abel
  · intro x
    simp [quantumPositiveKernel, hf0]
  · intro s c
    have h := hf.finite_test (fun x : s => (x : Fin d → ℂ)) (fun x : s => c x)
    have hreal := (Complex.nonneg_iff.mp h).1
    have hsum : (∑ i : s, ∑ j : s, star (c i) * c j *
        quantumPositiveKernel f r i j) =
        ∑ x ∈ s, ∑ y ∈ s, star (c x) * c y * quantumPositiveKernel f r x y := by
      calc
        _ = ∑ i : s, ∑ y ∈ s, star (c i) * c y * quantumPositiveKernel f r i y := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_coe_sort s (fun y =>
            star (c i) * c y * quantumPositiveKernel f r i y)
        _ = _ := Finset.sum_coe_sort s (fun x =>
          ∑ y ∈ s, star (c x) * c y * quantumPositiveKernel f r x y)
    rwa [hsum] at hreal

end Cloning.MultimodeCoherent
