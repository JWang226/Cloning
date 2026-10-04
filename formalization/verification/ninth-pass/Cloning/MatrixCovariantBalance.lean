import Cloning.CartanChannel
import Cloning.MatrixPartialTraceCovariance
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Schur scalarity and balanced partial traces

This file uses Mathlib's irreducible-representation Schur lemma over the
algebraically closed complex numbers. Scalarity is a proved consequence
of an actual irreducible representation, rather than an additional axiom.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
open Matrix

namespace Cloning.MatrixCovariantBalance

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {G A : Type*} [Monoid G] [Fintype A] [DecidableEq A]

/-- Schur's lemma for the concrete matrices of an irreducible complex
representation: every commuting matrix is scalar. -/
theorem commuting_matrix_is_scalar
    (ρ : Representation ℂ G (A → ℂ)) [Representation.IsIrreducible ρ]
    (M : Matrix A A ℂ)
    (hcomm : ∀ g, M * LinearMap.toMatrix' (ρ g) = LinearMap.toMatrix' (ρ g) * M) :
    ∃ c : ℂ, M = c • (1 : Matrix A A ℂ) := by
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := Matrix.toLin' M
      isIntertwining' := fun g => by
        have h := congrArg Matrix.toLin' (hcomm g)
        simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix'] using h }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  refine ⟨c, ?_⟩
  have hlin := congrArg (fun h : Representation.IntertwiningMap ρ ρ => h.toLinearMap) hc
  have hmat := congrArg LinearMap.toMatrix' hlin
  have hId : (1 : Representation.IntertwiningMap ρ ρ).toLinearMap = LinearMap.id := rfl
  simpa [f, Representation.IntertwiningMap.algebraMap_apply, hId] using hmat.symm

/-- The scalar in Schur's lemma is determined by the normalized trace. -/
theorem commuting_matrix_eq_trace_smul
    (ρ : Representation ℂ G (A → ℂ)) [Representation.IsIrreducible ρ]
    (M : Matrix A A ℂ) (hA : 0 < Fintype.card A)
    (hcomm : ∀ g, M * LinearMap.toMatrix' (ρ g) = LinearMap.toMatrix' (ρ g) * M) :
    M = (Matrix.trace M / (Fintype.card A : ℂ)) • (1 : Matrix A A ℂ) := by
  obtain ⟨c, hc⟩ := commuting_matrix_is_scalar ρ M hcomm
  have htr : Matrix.trace M = c * (Fintype.card A : ℂ) := by
    rw [hc, Matrix.trace_smul, Matrix.trace_one]
    rfl
  have hcard : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
  have hscalar : c = Matrix.trace M / (Fintype.card A : ℂ) :=
    (eq_div_iff hcard).mpr htr.symm
  exact hc.trans (congrArg (fun z : ℂ => z • (1 : Matrix A A ℂ)) hscalar)

variable {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

omit [DecidableEq A] [DecidableEq B] in
/-- The finite partial trace preserves the total trace. -/
theorem trace_partialTrace (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (Cloning.Compression.partialTrace Y) = Matrix.trace Y := by
  simp only [Matrix.trace, Matrix.diag, Cloning.Compression.partialTrace,
    Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] in
/-- The partial trace of an isometric range projection has the inclusion
space's dimension as its trace. -/
theorem trace_partialTrace_isometry (V : Matrix (A × B) C ℂ)
    (hV : V.conjTranspose * V = 1) :
    Matrix.trace (Cloning.Compression.partialTrace (V * V.conjTranspose)) = Fintype.card C := by
  rw [trace_partialTrace, Matrix.trace_mul_comm, hV, Matrix.trace_one]

omit [DecidableEq B] in
/-- A commuting partial trace is balanced by irreducibility, with its
constant fixed by the actual matrix dimensions and the isometry identity. -/
theorem balanced_partialTrace_of_commuting
    (ρ : Representation ℂ G (A → ℂ)) [Representation.IsIrreducible ρ]
    (V : Matrix (A × B) C ℂ) (hA : 0 < Fintype.card A)
    (hV : V.conjTranspose * V = 1)
    (hcomm : ∀ g,
      Cloning.Compression.partialTrace (V * V.conjTranspose) * LinearMap.toMatrix' (ρ g) =
        LinearMap.toMatrix' (ρ g) * Cloning.Compression.partialTrace (V * V.conjTranspose)) :
    Cloning.Compression.partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  rw [commuting_matrix_eq_trace_smul ρ _ hA hcomm, trace_partialTrace_isometry V hV]
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]

/-- Unitary conjugation invariance gives the commuting operator needed by
Schur's lemma. -/
theorem commutes_of_conjugation_invariant (U M : Matrix A A ℂ)
    (hU : U.conjTranspose * U = 1) (hM : U * M * U.conjTranspose = M) :
    M * U = U * M := by
  have h := congrArg (fun X : Matrix A A ℂ => X * U) hM
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one] at h
  exact h.symm

omit [DecidableEq B] in
/-- The balancing identity follows from actual unitary invariance and
irreducibility; scalarity is derived using Schur's lemma. -/
theorem balanced_partialTrace_of_invariant
    (ρ : Representation ℂ G (A → ℂ)) [Representation.IsIrreducible ρ]
    (V : Matrix (A × B) C ℂ) (hA : 0 < Fintype.card A)
    (hV : V.conjTranspose * V = 1)
    (hunitary : ∀ g, (LinearMap.toMatrix' (ρ g)).conjTranspose * LinearMap.toMatrix' (ρ g) = 1)
    (hinvariant : ∀ g,
      LinearMap.toMatrix' (ρ g) * Cloning.Compression.partialTrace (V * V.conjTranspose) *
        (LinearMap.toMatrix' (ρ g)).conjTranspose =
          Cloning.Compression.partialTrace (V * V.conjTranspose)) :
    Cloning.Compression.partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  apply balanced_partialTrace_of_commuting ρ V hA hV
  intro g
  exact commutes_of_conjugation_invariant _ _ (hunitary g) (hinvariant g)

/-- Balanced partial trace from an actual isometric intertwiner of unitary
representations. Irreducibility is required only on the retained factor.
All partial-trace covariance, Schur scalarity, and dimension normalization
steps are proved; there is no balancing assumption. -/
theorem balanced_partialTrace_of_intertwining
    (ρ : Representation ℂ G (A → ℂ))
    (σ : Representation ℂ G (B → ℂ))
    (τ : Representation ℂ G (C → ℂ))
    [Representation.IsIrreducible ρ]
    (V : Matrix (A × B) C ℂ) (hA : 0 < Fintype.card A)
    (hV : V.conjTranspose * V = 1)
    (hρ : ∀ g, (LinearMap.toMatrix' (ρ g)).conjTranspose * LinearMap.toMatrix' (ρ g) = 1)
    (hσ : ∀ g, (LinearMap.toMatrix' (σ g)).conjTranspose * LinearMap.toMatrix' (σ g) = 1)
    (hτ : ∀ g, LinearMap.toMatrix' (τ g) * (LinearMap.toMatrix' (τ g)).conjTranspose = 1)
    (hintertwine : ∀ g, (LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (σ g)) * V =
      V * LinearMap.toMatrix' (τ g)) :
    Cloning.Compression.partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  apply balanced_partialTrace_of_commuting ρ V hA hV
  intro g
  exact Cloning.Compression.partialTrace_intertwiner_commutes
    (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (σ g))
    (LinearMap.toMatrix' (τ g)) V (hρ g) (hσ g) (hτ g) (hintertwine g)

/-- The Cartan-sector channel constructed from irreducible unitary
representation data and an isometric intertwiner. Its complete positivity
and trace preservation are obtained without a partial-trace balance premise. -/
def cartanChannel_of_irreducible_intertwiner
    (ρ : Representation ℂ G (A → ℂ))
    (σ : Representation ℂ G (B → ℂ))
    (τ : Representation ℂ G (C → ℂ))
    [Representation.IsIrreducible ρ]
    (V : Matrix (A × B) C ℂ)
    (hA : 0 < Fintype.card A) (hC : 0 < Fintype.card C)
    (hV : V.conjTranspose * V = 1)
    (hρ : ∀ g, (LinearMap.toMatrix' (ρ g)).conjTranspose * LinearMap.toMatrix' (ρ g) = 1)
    (hσ : ∀ g, (LinearMap.toMatrix' (σ g)).conjTranspose * LinearMap.toMatrix' (σ g) = 1)
    (hτ : ∀ g, LinearMap.toMatrix' (τ g) * (LinearMap.toMatrix' (τ g)).conjTranspose = 1)
    (hintertwine : ∀ g, (LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (σ g)) * V =
      V * LinearMap.toMatrix' (τ g)) : Cloning.Channels.MatrixChannel A C :=
  Cloning.CartanChannel.cartanChannel V (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (Nat.cast_pos.mpr hA) (Nat.cast_pos.mpr hC)
    (balanced_partialTrace_of_intertwining ρ σ τ V hA hV hρ hσ hτ hintertwine)

/-- The channel obtained from representation data has exactly the Cartan
formula stated in the manuscript. -/
theorem cartanChannel_of_irreducible_intertwiner_apply
    (ρ : Representation ℂ G (A → ℂ))
    (σ : Representation ℂ G (B → ℂ))
    (τ : Representation ℂ G (C → ℂ))
    [Representation.IsIrreducible ρ]
    (V : Matrix (A × B) C ℂ)
    (hA : 0 < Fintype.card A) (hC : 0 < Fintype.card C)
    (hV : V.conjTranspose * V = 1)
    (hρ : ∀ g, (LinearMap.toMatrix' (ρ g)).conjTranspose * LinearMap.toMatrix' (ρ g) = 1)
    (hσ : ∀ g, (LinearMap.toMatrix' (σ g)).conjTranspose * LinearMap.toMatrix' (σ g) = 1)
    (hτ : ∀ g, LinearMap.toMatrix' (τ g) * (LinearMap.toMatrix' (τ g)).conjTranspose = 1)
    (hintertwine : ∀ g, (LinearMap.toMatrix' (ρ g) ⊗ₖ LinearMap.toMatrix' (σ g)) * V =
      V * LinearMap.toMatrix' (τ g)) (X : Matrix A A ℂ) :
    (cartanChannel_of_irreducible_intertwiner ρ σ τ V hA hC hV hρ hσ hτ hintertwine).toFun X =
      Cloning.Compression.sectorMap (Fintype.card A : ℝ) (Fintype.card C : ℝ) V X := by
  apply Cloning.CartanChannel.cartanChannel_apply

end Cloning.MatrixCovariantBalance
