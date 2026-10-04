import Cloning.TensorPBWSpanning
import Cloning.TensorPBWNormalization

/-! Exact fixed-cutoff physical PBW bases. Spanning is proved by physical
straightening and independence by the actual finite Gram limit. -/
noncomputable section
open scoped BigOperators InnerProductSpace Topology
open Filter Module
namespace Cloning.TensorLie
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

local instance : FiniteDimensional ℂ (TensorRegister n (Fin d)) :=
  (Cloning.PCT.registerBasis (Fin n → Fin d)).toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- Canonical oscillator-normalized occupation vectors in the literal physical
root-height cutoff. -/
def canonicalCutoffVector (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (k : HeightOccupation d R) : cyclicCutoff Ω (R : ℤ) :=
  ⟨normalizedLoweringWord Ω mu (canonicalWord k.val),
    normalizedLoweringWord_mem_cyclicCutoff Ω mu _ (by
      rw [canonicalWord_height]
      exact_mod_cast k.property)⟩

@[simp] theorem canonicalCutoffVector_coe (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ) (k : HeightOccupation d R) :
    (canonicalCutoffVector Ω mu R k : TensorRegister n (Fin d)) =
      normalizedLoweringWord Ω mu (canonicalWord k.val) := rfl

theorem span_canonicalCutoffVector_eq_top (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2) :
    Submodule.span ℂ (Set.range (canonicalCutoffVector Ω mu R)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (cyclicCutoff Ω (R : ℤ)) _).mpr
  rw [span_normalizedLoweringWord_eq Ω mu hgap, cyclicCutoff_eq_span_canonical]

def canonicalCutoffBasis (Ω : TensorRegister n (Fin d)) (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d R =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) :
    Basis (HeightOccupation d R) ℂ (cyclicCutoff Ω (R : ℤ)) :=
  Basis.mk
    (LinearIndependent.of_comp (v := canonicalCutoffVector Ω mu R)
      (cyclicCutoff Ω (R : ℤ)).subtype (by
        change LinearIndependent ℂ (fun k : HeightOccupation d R =>
          normalizedLoweringWord Ω mu (canonicalWord k.val))
        exact hli))
    (span_canonicalCutoffVector_eq_top Ω mu R hgap).ge

@[simp] theorem canonicalCutoffBasis_coe (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d R =>
      normalizedLoweringWord Ω mu (canonicalWord k.val))) (k : HeightOccupation d R) :
    (canonicalCutoffBasis Ω mu R hgap hli k : TensorRegister n (Fin d)) =
      normalizedLoweringWord Ω mu (canonicalWord k.val) := by
  rw [canonicalCutoffBasis, Basis.mk_apply]
  rfl

theorem canonicalCutoffBasis_cartan (Ω : TensorRegister n (Fin d))
    (mu : Fin d → ℕ) (R : ℕ)
    (hweight : ∀ a, collectiveGenerator n a a Ω = (mu a : ℂ) • Ω)
    (hgap : ∀ a : PositiveRoot d, 0 < (mu a.val.1 : ℝ) - mu a.val.2)
    (hli : LinearIndependent ℂ (fun k : HeightOccupation d R =>
      normalizedLoweringWord Ω mu (canonicalWord k.val)))
    (k : HeightOccupation d R) (a : Fin d) :
    collectiveGenerator n a a
      (canonicalCutoffBasis Ω mu R hgap hli k : TensorRegister n (Fin d)) =
      ((mu a : ℂ) + (∑ r : PositiveRoot d, (k.val r : ℤ) * r.weight a : ℤ)) •
        (canonicalCutoffBasis Ω mu R hgap hli k : TensorRegister n (Fin d)) := by
  simp only [canonicalCutoffBasis_coe, cartan_normalizedLoweringWord Ω mu hweight,
    canonicalWord_weight]

/-- Every fixed height cutoff eventually has exactly its canonical physical
occupation basis. Neither independence nor spanning is a hypothesis. All
positive-root gaps must tend to infinity; a retained subset alone does not
span the full cutoff. -/
theorem partition_eventually_canonicalCutoffBasis
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2) (R : ℕ) :
    ∀ᶠ N in atTop, ∃ b : Basis (HeightOccupation d R) ℂ
      (cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ)),
      ∀ k, (b k : TensorRegister (∑ a, mu N a) (Fin d)) =
        normalizedLoweringWord (partitionHighestTensor (mu N) (hmu N)) (mu N)
          (canonicalWord k.val) := by
  classical
  have hwords : ∀ k l : HeightOccupation d R,
      (canonicalWord k.val).Perm (canonicalWord l.val) ↔ k = l := by
    intro k l
    rw [canonicalWord_perm_iff, Subtype.val_inj]
  have hli := partition_normalizedWord_eventually_linearIndependent
    (fun a : PositiveRoot d => a) Function.injective_id mu hmu δ hδ hgap
    (fun k : HeightOccupation d R => canonicalWord k.val) hwords
  have hpos : ∀ᶠ N in atTop, 0 < δ N := hδ.eventually (eventually_gt_atTop 0)
  filter_upwards [hli, hgap, hpos] with N hN hg hp
  have hg' : ∀ a : PositiveRoot d, 0 < (mu N a.val.1 : ℝ) - mu N a.val.2 :=
    fun a => hp.trans_le (hg a)
  exact ⟨canonicalCutoffBasis _ _ R hg' hN, canonicalCutoffBasis_coe _ _ R hg' hN⟩

/-- The eventual dimension is the exact number of root occupations under the
weighted cutoff, as a consequence of the constructed physical basis. -/
theorem partition_eventually_finrank_cyclicCutoff
    (mu : ℕ → Fin d → ℕ) (hmu : ∀ N, Antitone (mu N))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop atTop)
    (hgap : ∀ᶠ N in atTop, ∀ a : PositiveRoot d,
      δ N ≤ (mu N a.val.1 : ℝ) - mu N a.val.2) (R : ℕ) :
    ∀ᶠ N in atTop,
      Module.finrank ℂ (cyclicCutoff (partitionHighestTensor (mu N) (hmu N)) (R : ℤ)) =
        Fintype.card (HeightOccupation d R) := by
  filter_upwards [partition_eventually_canonicalCutoffBasis mu hmu δ hδ hgap R] with N hN
  obtain ⟨b, _⟩ := hN
  exact Module.finrank_eq_card_basis b

end Cloning.TensorLie
