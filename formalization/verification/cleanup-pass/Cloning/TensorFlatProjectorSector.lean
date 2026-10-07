import Cloning.TensorFlatProjectorSupport

/-! The supported part of an ambient physical sector is the literal
coordinate image of the smaller-rank cyclic sector. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Cloning.TensorLie
open Cloning.PCT
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r k : ℕ}

def coordinateRoot (a : PositiveRoot r) : PositiveRoot (r+k) :=
  ⟨(Fin.castAdd k a.val.1, Fin.castAdd k a.val.2), a.property⟩

theorem coordinateTensorEmbedding_loweringWord (Ω : TensorRegister n (Fin r))
    (w : List (PositiveRoot r)) :
    coordinateTensorEmbedding n r k (loweringWord Ω w) =
      loweringWord (coordinateTensorEmbedding n r k Ω) (w.map coordinateRoot) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, loweringWord, coordinateRoot]
    rw [coordinateTensorEmbedding_collective, ih]

/-- The lowering span is closed under every lowering generator without any
highest-vector assumptions. -/
theorem cyclicSector_lowering_invariant {d : ℕ} (Ω : TensorRegister n (Fin d))
    (a : PositiveRoot d) {x : TensorRegister n (Fin d)} (hx : x ∈ cyclicSector Ω) :
    collectiveGenerator n a.val.2 a.val.1 x ∈ cyclicSector Ω := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    exact loweringWord_mem_cyclicSector Ω (a::w)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (cyclicSector Ω).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (cyclicSector Ω).smul_mem c ih

theorem coordinateTensorEmbedding_mem_cyclicSector (Ω : TensorRegister n (Fin r))
    {x : TensorRegister n (Fin r)} (hx : x ∈ cyclicSector Ω) :
    coordinateTensorEmbedding n r k x ∈ cyclicSector (coordinateTensorEmbedding n r k Ω) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    rw [coordinateTensorEmbedding_loweringWord]
    exact loweringWord_mem_cyclicSector _ _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- Coordinate inclusion restricted to the actual cyclic Hilbert spaces. -/
def coordinateSectorEmbedding (Ω : TensorRegister n (Fin r)) :
    cyclicSector Ω →ₗᵢ[ℂ] cyclicSector (coordinateTensorEmbedding n r k Ω) where
  toLinearMap := {
    toFun x := ⟨coordinateTensorEmbedding n r k x, coordinateTensorEmbedding_mem_cyclicSector Ω x.property⟩
    map_add' x y := Subtype.ext (map_add _ _ _)
    map_smul' c x := Subtype.ext (map_smul _ _ _) }
  norm_map' x := (coordinateTensorEmbedding n r k).norm_map x

@[simp] theorem coordinateSectorEmbedding_coe (Ω : TensorRegister n (Fin r)) (x : cyclicSector Ω) :
    (coordinateSectorEmbedding (k := k) Ω x : TensorRegister n (Fin (r+k))) =
      coordinateTensorEmbedding n r k x := rfl

/-- Projecting any ambient lowering word leaves only supported lowering words. -/
theorem coordinateTensorProjection_mem_image_word (Ω : TensorRegister n (Fin r))
    (w : List (PositiveRoot (r+k))) :
    coordinateTensorProjection n r k (loweringWord (coordinateTensorEmbedding n r k Ω) w) ∈
      (cyclicSector Ω).map (coordinateTensorEmbedding n r k).toLinearMap := by
  induction w with
  | nil =>
    rw [loweringWord, coordinateTensorProjection_embedding]
    exact ⟨Ω,highest_mem_cyclicSector Ω,rfl⟩
  | cons a w ih =>
    rcases a with ⟨⟨lo,hi⟩,hlt⟩
    change coordinateTensorProjection n r k
      (collectiveGenerator n hi lo (loweringWord _ w)) ∈ _
    induction hi using Fin.addCases with
    | right hi =>
      rw [coordinateTensorProjection_collective_outside]
      exact Submodule.zero_mem _
    | left hi =>
      induction lo using Fin.addCases with
      | right lo =>
        have hh : r+lo.val < hi.val := hlt
        omega
      | left lo =>
        rw [coordinateTensorProjection_collective]
        obtain ⟨x,hx,he⟩ := ih
        rw [← he]
        simp only [LinearIsometry.coe_toLinearMap]
        rw [← coordinateTensorEmbedding_collective]
        exact ⟨_,cyclicSector_lowering_invariant Ω ⟨(lo,hi),hlt⟩ hx,rfl⟩

/-- Exact support-range identification on the full physical cyclic sector. -/
theorem coordinateTensorProjection_mem_image (Ω : TensorRegister n (Fin r))
    {x : TensorRegister n (Fin (r+k))}
    (hx : x ∈ cyclicSector (coordinateTensorEmbedding n r k Ω)) :
    coordinateTensorProjection n r k x ∈
      (cyclicSector Ω).map (coordinateTensorEmbedding n r k).toLinearMap := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,rfl⟩ := hx
    exact coordinateTensorProjection_mem_image_word Ω w
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

end Cloning.TensorLie
