import Cloning.WeylGaussianVacuumSpace

/-! Every unit vacuum vector of a regular Weyl representation generates an
actual isometric copy of multimode Fock space. -/
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexOrder

namespace Cloning.WeylGNS
open MultimodeCoherent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (W : RegularWeyl d H)

theorem RegularWeyl.inner_operator_pair (a b : Fin d → ℂ) (x y : H) :
    ⟪W.operator a x, W.operator b y⟫_ℂ =
      displacementPhase (-a) b * ⟪x, W.operator (b-a) y⟫_ℂ := by
  rw [W.inner_operator]
  change ⟪x, W.toIsometry (-a) (W.toIsometry b y)⟫_ℂ = _
  rw [W.mul_apply, inner_smul_right]
  simp only [neg_add_eq_sub, RegularWeyl.operator_apply]

theorem coherent_inner_phase_gaussian (a b : Fin d → ℂ) :
    ⟪coherentVector a, coherentVector b⟫_ℂ = displacementPhase (-a) b *
      (gaussianWeight (fun _ : Fin d => (1/2:ℝ)) (b-a) : ℂ) := by
  have hh := (fockRegularWeyl d).inner_operator_pair a b (coherentVector 0) (coherentVector 0)
  change ⟪displacement a (coherentVector 0), displacement b (coherentVector 0)⟫_ℂ =
    displacementPhase (-a) b * ⟪coherentVector 0, displacement (b-a) (coherentVector 0)⟫_ℂ at hh
  rw [displacement_vacuum, displacement_vacuum, vacuum_characteristic] at hh
  rw [hh]
  congr 1
  simp only [gaussianWeight, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  ring

theorem RegularWeyl.inner_vacuum_translates (a b : Fin d → ℂ) (x y : W.vacuumSpace) :
    ⟪W.operator a (x : H), W.operator b (y : H)⟫_ℂ =
      ⟪coherentVector a, coherentVector b⟫_ℂ * ⟪(x : H), (y : H)⟫_ℂ := by
  rw [W.translated_vacuum_inner, coherent_inner_phase_gaussian]

def RegularWeyl.vacuumCombination (x : W.vacuumSpace) : ((Fin d → ℂ) →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun a => W.operator a (x : H))

theorem RegularWeyl.inner_vacuumCombination (x y : W.vacuumSpace)
    (c e : (Fin d → ℂ) →₀ ℂ) :
    ⟪W.vacuumCombination x c, W.vacuumCombination y e⟫_ℂ =
      ⟪coherentCombination c, coherentCombination e⟫_ℂ * ⟪(x : H), (y : H)⟫_ℂ := by
  simp only [RegularWeyl.vacuumCombination, coherentCombination,
    Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, sum_inner,
    inner_smul_left, inner_smul_right, W.inner_vacuum_translates,
    Finset.sum_mul, mul_assoc]

theorem RegularWeyl.norm_vacuumCombination (x : W.vacuumSpace) (hx : ‖(x : H)‖ = 1)
    (c : (Fin d → ℂ) →₀ ℂ) :
    ‖W.vacuumCombination x c‖ = ‖coherentCombination c‖ := by
  have h := W.inner_vacuumCombination x x c c
  have hxx : ⟪(x : H), (x : H)⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  rw [hxx, mul_one] at h
  have hh := congrArg Complex.re h
  change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _ at hh
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] at hh
  nlinarith [norm_nonneg (W.vacuumCombination x c), norm_nonneg (coherentCombination c)]

def RegularWeyl.vacuumEmbeddingMap (x : W.vacuumSpace) : Fock d →L[ℂ] H :=
  (W.vacuumCombination x).extendOfNorm coherentCombination

theorem RegularWeyl.vacuumEmbeddingMap_combination (x : W.vacuumSpace)
    (hx : ‖(x : H)‖ = 1) (c : (Fin d → ℂ) →₀ ℂ) :
    W.vacuumEmbeddingMap x (coherentCombination c) = W.vacuumCombination x c := by
  apply LinearMap.extendOfNorm_eq coherentCombination_dense
  exact ⟨1, fun c => by simp [W.norm_vacuumCombination x hx]⟩

theorem RegularWeyl.vacuumEmbeddingMap_coherent (x : W.vacuumSpace)
    (hx : ‖(x : H)‖ = 1) (a : Fin d → ℂ) :
    W.vacuumEmbeddingMap x (coherentVector a) = W.operator a (x : H) := by
  have h := W.vacuumEmbeddingMap_combination x hx (Finsupp.single a 1)
  simpa [coherentCombination, RegularWeyl.vacuumCombination] using h

theorem RegularWeyl.vacuumEmbeddingMap_norm (x : W.vacuumSpace)
    (hx : ‖(x : H)‖ = 1) (v : Fock d) : ‖W.vacuumEmbeddingMap x v‖ = ‖v‖ := by
  refine coherentCombination_dense.induction_on
    (p := fun v => ‖W.vacuumEmbeddingMap x v‖ = ‖v‖) v
    (isClosed_eq ((W.vacuumEmbeddingMap x).continuous.norm) continuous_norm) ?_
  intro c
  rw [W.vacuumEmbeddingMap_combination x hx, W.norm_vacuumCombination x hx]

def RegularWeyl.vacuumEmbedding (x : W.vacuumSpace) (hx : ‖(x : H)‖ = 1) :
    Fock d →ₗᵢ[ℂ] H where
  toLinearMap := (W.vacuumEmbeddingMap x).toLinearMap
  norm_map' := W.vacuumEmbeddingMap_norm x hx

@[simp] theorem RegularWeyl.vacuumEmbedding_coherent (x : W.vacuumSpace)
    (hx : ‖(x : H)‖ = 1) (a : Fin d → ℂ) :
    W.vacuumEmbedding x hx (coherentVector a) = W.operator a (x : H) :=
  W.vacuumEmbeddingMap_coherent x hx a

end Cloning.WeylGNS
