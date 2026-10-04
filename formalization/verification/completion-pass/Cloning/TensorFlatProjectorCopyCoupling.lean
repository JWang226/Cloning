import Cloning.TensorFlatProjectorMixture
import Cloning.TensorLANEmbeddingSelector

/-! Exact uniform lifting of a physical label coupling to the actual Schur copies. -/
noncomputable section
open scoped BigOperators Classical
namespace Cloning.TensorCloning
open Cloning.TensorLie Cloning.TensorLAN Cloning.YoungGeneral
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

section Finite
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]

theorem sum_by_label (labels : I → A) (f : A → ℝ) :
    ∑ i, f (labels i) = ∑ a, (labelMultiplicity labels a : ℝ) * f a := by
  calc
    _ = ∑ i : I, ∑ a : A, if labels i=a then f a else 0 := by simp
    _ = ∑ a : A, ∑ i : I, if labels i=a then f a else 0 := Finset.sum_comm
    _ = _ := by simp [labelMultiplicity, Finset.sum_ite, mul_comm]

theorem sum_uniform_copies (labels : I → A) (f : A → ℝ)
    (hf : ∀ a, labelMultiplicity labels a=0 → f a=0) :
    ∑ i, f (labels i)/(labelMultiplicity labels (labels i) : ℝ) = ∑ a, f a := by
  rw [sum_by_label labels (fun a => f a/(labelMultiplicity labels a : ℝ))]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : labelMultiplicity labels a=0
  · simp [ha,hf a ha]
  · field_simp

def uniformCopyCoupling (l : I → A) (r : J → B) (K : A → B → ℝ) (i : I) (j : J) : ℝ :=
  K (l i) (r j) / ((labelMultiplicity l (l i) : ℝ)*(labelMultiplicity r (r j) : ℝ))

theorem labelMultiplicity_pos_at (l : I → A) (i : I) : 0 < labelMultiplicity l (l i) := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [labelMultiplicity]⟩

theorem uniformCopyCoupling_row (l : I → A) (r : J → B) (K : A → B → ℝ)
    (v : A → ℝ) (w : B → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑ b, K a b = (labelMultiplicity l a : ℝ)*v a)
    (hcol : ∀ b, ∑ a, K a b = (labelMultiplicity r b : ℝ)*w b) (i : I) :
    ∑ j, uniformCopyCoupling l r K i j = v (l i) := by
  have hz (b : B) (hb : labelMultiplicity r b=0) : K (l i) b=0 := by
    have he := Finset.single_le_sum (fun a _ => hK a b) (Finset.mem_univ (l i))
    rw [hcol,hb,Nat.cast_zero,zero_mul] at he
    exact le_antisymm he (hK _ _)
  have he : (∑ j, uniformCopyCoupling l r K i j) =
      (∑ j, K (l i) (r j)/(labelMultiplicity r (r j) : ℝ))/(labelMultiplicity l (l i) : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    unfold uniformCopyCoupling
    ring
  rw [he,sum_uniform_copies r _ hz,hrow]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (labelMultiplicity_pos_at l i).ne')

theorem uniformCopyCoupling_col (l : I → A) (r : J → B) (K : A → B → ℝ)
    (v : A → ℝ) (w : B → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑ b, K a b = (labelMultiplicity l a : ℝ)*v a)
    (hcol : ∀ b, ∑ a, K a b = (labelMultiplicity r b : ℝ)*w b) (j : J) :
    ∑ i, uniformCopyCoupling l r K i j = w (r j) := by
  have he := uniformCopyCoupling_row r l (fun b a => K a b) w v
    (fun b a => hK a b) hcol hrow j
  simpa only [uniformCopyCoupling, mul_comm] using he

theorem uniformCopyCoupling_observable (l : I → A) (r : J → B) (K : A → B → ℝ)
    (hzeroL : ∀ a b, labelMultiplicity l a=0 → K a b=0)
    (hzeroR : ∀ a b, labelMultiplicity r b=0 → K a b=0) (f : A → B → ℝ) :
    ∑ i : I, ∑ j : J, uniformCopyCoupling l r K i j*f (l i) (r j) =
      ∑ a : A, ∑ b : B, K a b*f a b := by
  have hi (i : I) : (∑ j : J, uniformCopyCoupling l r K i j*f (l i) (r j)) =
      ∑ b : B, (K (l i) b*f (l i) b)/(labelMultiplicity l (l i) : ℝ) := by
    have he : (∑ j : J, uniformCopyCoupling l r K i j*f (l i) (r j)) =
        ∑ j : J, ((K (l i) (r j)*f (l i) (r j))/(labelMultiplicity l (l i) : ℝ)) /
          (labelMultiplicity r (r j) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold uniformCopyCoupling
      ring
    rw [he]
    exact sum_uniform_copies r (fun b => K (l i) b*f (l i) b/(labelMultiplicity l (l i) : ℝ))
      (fun b hb => by simp only [hzeroR (l i) b hb, zero_mul, zero_div])
  simp_rw [hi]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : B, ∑ a : A, K a b*f a b := by
      apply Finset.sum_congr rfl
      intro b _
      exact sum_uniform_copies l (fun a => K a b*f a b)
        (fun a ha => by simp only [hzeroL a b ha, zero_mul])
    _ = _ := Finset.sum_comm
end Finite

variable {n m d : ℕ}
def physicalCopyShape (n d : ℕ) (i : SchurCopy n d) : Shape d n :=
  ((recursivePhysicalDecomposition n d).get i).shape

theorem physicalCopyShape_multiplicity (mu : Shape d n) :
    labelMultiplicity (physicalCopyShape n d) mu =
      physicalCopyCount (recursivePhysicalDecomposition n d) (fun a => (mu a).val) := by
  unfold labelMultiplicity physicalCopyCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact PhysicalHighestTensor.shape_eq_iff _ mu

def labelCouplingCopies (K : Shape d n → Shape d m → ℝ) :=
  uniformCopyCoupling (physicalCopyShape n d) (physicalCopyShape m d) K

theorem labelCouplingCopies_nonneg (K : Shape d n → Shape d m → ℝ)
    (hK : ∀ mu lam, 0 ≤ K mu lam) (i : SchurCopy n d) (j : SchurCopy m d) :
    0 ≤ labelCouplingCopies K i j := by
  exact div_nonneg (hK _ _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem labelCouplingCopies_row (p : Fin d → ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1)
    (K : Shape d n → Shape d m → ℝ) (hK : ∀ mu lam,0≤K mu lam)
    (hrow : ∀ mu, ∑ lam,K mu lam=(tensorYoungPMF n d p hp hs mu).toReal)
    (hcol : ∀ lam, ∑ mu,K mu lam=(tensorYoungPMF m d p hp hs lam).toReal)
    (i : SchurCopy n d) : ∑ j,labelCouplingCopies K i j=knownCopyWeight n d p i := by
  have hr (mu : Shape d n) : ∑ lam,K mu lam=
      (labelMultiplicity (physicalCopyShape n d) mu : ℝ)*physicalSectorCharacter (fun a=>(mu a).val) p := by
    rw [hrow, tensorYoungPMF, physicalYoungPMF_toReal, physicalCopyShape_multiplicity]
  have hc (lam : Shape d m) : ∑ mu,K mu lam=
      (labelMultiplicity (physicalCopyShape m d) lam : ℝ)*physicalSectorCharacter (fun a=>(lam a).val) p := by
    rw [hcol, tensorYoungPMF, physicalYoungPMF_toReal, physicalCopyShape_multiplicity]
  exact (uniformCopyCoupling_row _ _ K _ _ hK hr hc i).trans
    (PhysicalHighestTensor.character_eq_physicalSectorCharacter _ p).symm

theorem labelCouplingCopies_col (p : Fin d → ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1)
    (K : Shape d n → Shape d m → ℝ) (hK : ∀ mu lam,0≤K mu lam)
    (hrow : ∀ mu, ∑ lam,K mu lam=(tensorYoungPMF n d p hp hs mu).toReal)
    (hcol : ∀ lam, ∑ mu,K mu lam=(tensorYoungPMF m d p hp hs lam).toReal)
    (j : SchurCopy m d) : ∑ i,labelCouplingCopies K i j=knownCopyWeight m d p j := by
  have he := labelCouplingCopies_row p hp hs (fun lam mu => K mu lam) (fun lam mu => hK mu lam)
    hcol hrow j
  simpa only [labelCouplingCopies,uniformCopyCoupling,mul_comm] using he

theorem labelCouplingCopies_observable (p : Fin d → ℝ) (hp : ∀a,0≤p a) (hs : ∑a,p a=1)
    (K : Shape d n → Shape d m → ℝ) (hK : ∀ mu lam,0≤K mu lam)
    (hrow : ∀ mu, ∑ lam,K mu lam=(tensorYoungPMF n d p hp hs mu).toReal)
    (hcol : ∀ lam, ∑ mu,K mu lam=(tensorYoungPMF m d p hp hs lam).toReal)
    (f : Shape d n → Shape d m → ℝ) :
    ∑ i, ∑ j, labelCouplingCopies K i j*f (physicalCopyShape n d i) (physicalCopyShape m d j) =
      ∑ mu, ∑ lam, K mu lam*f mu lam := by
  apply uniformCopyCoupling_observable
  · intro mu lam hz
    have he := Finset.single_le_sum (fun lam _ => hK mu lam) (Finset.mem_univ lam)
    rw [hrow,tensorYoungPMF,physicalYoungPMF_toReal,← physicalCopyShape_multiplicity,hz,
      Nat.cast_zero,zero_mul] at he
    exact le_antisymm he (hK _ _)
  · intro mu lam hz
    have he := Finset.single_le_sum (fun mu _ => hK mu lam) (Finset.mem_univ mu)
    rw [hcol,tensorYoungPMF,physicalYoungPMF_toReal,← physicalCopyShape_multiplicity,hz,
      Nat.cast_zero,zero_mul] at he
    exact le_antisymm he (hK _ _)

end Cloning.TensorCloning
