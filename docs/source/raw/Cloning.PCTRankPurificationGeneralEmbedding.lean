import Cloning.PhysicalFlatGrassmannEmbedding

/-! Every actual density of rank at most r factors through an r-dimensional
physical system. The support embedding and the internal state are constructed
from the density's spectral theorem, including states of smaller rank. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Cloning.PCTRankPurification
open Cloning.MatrixFidelity Cloning.PCTPhysicalState Cloning.PhysicalFlatGrassmann
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Positivity and the literal matrix-rank bound force all ordered
spectral values past the first r positions to vanish. -/
theorem orderedEigenvalues_zero_of_rank_le {r k : ℕ}
    (ρ : State (Fin (r+k))) (hrank : ρ.matrix.rank≤r)
    (i : Fin (r+k)) (hi : r≤ i.val) : orderedEigenvalues ρ i=0 := by
  classical
  by_contra hne
  have hpos : 0<orderedEigenvalues ρ i :=
    lt_of_le_of_ne (ρ.positive.eigenvalues_nonneg _) (Ne.symm hne)
  let f : Fin (r+1) → {j : Fin (r+k) // ρ.positive.isHermitian.eigenvalues j≠0} :=
    fun a => ⟨orderedIndex (r+k) ⟨a.val,by omega⟩,by
      have hle : (⟨a.val,by omega⟩ : Fin (r+k))≤ i := by simpa using (show a.val≤ i.val by omega)
      have hp := hpos.trans_le (orderedEigenvalues_antitone ρ hle)
      exact ne_of_gt hp⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := (orderedIndex (r+k)).injective (congrArg Subtype.val hab)
    exact Fin.ext (congrArg (fun x : Fin (r+k)=>x.val) h)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin,← ρ.positive.isHermitian.rank_eq_card_non_zero_eigs] at hc
  omega

/-- Coordinate inclusion of a smaller diagonal matrix is zero on every
unsupported coordinate. -/
theorem coordinateInclusion_diagonal (r k : ℕ) (p : Fin r→ℂ) :
    coordinateInclusion r k * Matrix.diagonal p * (coordinateInclusion r k)ᴴ =
      Matrix.diagonal (Fin.append p (fun _ : Fin k=>0)) := by
  classical
  have hcross (a : Fin r) (b : Fin k) : Fin.castAdd k a≠Fin.natAdd r b := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [coordinateInclusion,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply,hcross,eq_comm] <;> split_ifs <;> simp_all

/-- Literal rank at most r, with no support or diagonalization witness in
the assumptions, yields an isometric density-matrix factorization. -/
theorem exists_density_isometric_factor (r k : ℕ)
    (ρ : State (Fin (r+k))) (hrank : ρ.matrix.rank≤r) :
    ∃ J : Matrix (Fin (r+k)) (Fin r) ℂ, Jᴴ*J=1 ∧
      ∃σ : State (Fin r),ρ.matrix=J*σ.matrix*Jᴴ := by
  classical
  let p : Fin r→ℝ := fun i=>orderedEigenvalues ρ (Fin.castAdd k i)
  have hp : ∀i,0≤p i := fun i=>ρ.positive.eigenvalues_nonneg _
  have hz (i : Fin k) : orderedEigenvalues ρ (Fin.natAdd r i)=0 :=
    orderedEigenvalues_zero_of_rank_le ρ hrank _ (by simp)
  have hsum : ∑i,p i=1 := by
    have h := orderedEigenvalues_sum ρ
    rw [Fin.sum_univ_add] at h
    simpa only [hz,Finset.sum_const_zero,add_zero,p] using h
  let σ : State (Fin r) :=
    ⟨Matrix.diagonal (fun i=>(p i:ℂ)),Matrix.PosSemidef.diagonal (fun i=>by change (0:ℂ)≤(p i:ℂ); exact_mod_cast hp i),by
      rw [Matrix.trace_diagonal,← Complex.ofReal_sum,hsum,Complex.ofReal_one]⟩
  let U := orderedUnitary ρ
  let J := (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)*coordinateInclusion r k
  have hU : (U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)ᴴ*(U : Matrix (Fin (r+k)) (Fin (r+k)) ℂ)=1 :=
    Unitary.star_mul_self_of_mem U.property
  have hJ : Jᴴ*J=1 := by
    dsimp only [J]
    rw [Matrix.conjTranspose_mul]
    calc
      _=(coordinateInclusion r k)ᴴ*(U.valᴴ*U.val)*coordinateInclusion r k := by simp only [Matrix.mul_assoc]
      _=1 := by rw [hU,Matrix.mul_one,coordinateInclusion_isometry]
  refine ⟨J,hJ,σ,?_⟩
  have he : (fun i=>(orderedEigenvalues ρ i:ℂ))=
      Fin.append (fun i=>(p i:ℂ)) (fun _ : Fin k=>0) := by
    funext i
    induction i using Fin.addCases <;> simp [p,hz]
  rw [orderedUnitary_diagonalizes,he,← coordinateInclusion_diagonal]
  simp only [J,σ,U,Matrix.conjTranspose_mul,Matrix.mul_assoc]

local instance generalEmbedding_neZeroAmbient (r k : ℕ) [NeZero r] : NeZero (r+k) := ⟨by have := NeZero.ne r; omega⟩

/-- The matrix factorization also identifies the actual physical state. -/
theorem exists_embedded_density (r k : ℕ) [NeZero r]
    (ρ : State (Fin (r+k))) (hrank : ρ.matrix.rank≤r) :
    ∃ J : Matrix (Fin (r+k)) (Fin r) ℂ,∃ hJ : Jᴴ*J=1,
      ∃σ : State (Fin r),ρ=Cloning.PCTRankAdapted.embeddedState J hJ σ := by
  obtain ⟨J,hJ,σ,he⟩ := exists_density_isometric_factor r k ρ hrank
  refine ⟨J,hJ,σ,?_⟩
  cases ρ
  cases σ
  simpa only [Cloning.PCTRankAdapted.embeddedState,State.mk.injEq] using he

end Cloning.PCTRankPurification
