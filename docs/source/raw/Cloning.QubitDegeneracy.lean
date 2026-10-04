import Cloning.PhysicalCloningKnownTheorem
import Cloning.TensorCloningUniformCovariance
import Cloning.InfiniteFidelityHilbertSum

/-! Degeneracy and sample-size limits for the actual qubit cloning problem.
The constant channel is constructed as a completely positive, trace-preserving
map, and its convergence is uniform over the entire unitary orbit. -/
noncomputable section
open scoped BigOperators Topology Matrix ComplexOrder
open Filter
namespace Cloning.QubitDegeneracy
open Cloning.PCT Cloning.PCTPhysicalState Cloning.PCTUnitaryTransport
open Cloning.TensorCloning Cloning.InfiniteTraceClass Cloning.Hybrid
open Cloning.InfiniteFiniteCorner Cloning.PCTPurificationChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem state_eq_of_matrix_eq (ρ σ : MatrixFidelity.State (Fin 2))
    (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

def centralState : MatrixFidelity.State (Fin 2) :=
  diagonalState (fun _ => (1/2:ℝ)) (by intro i; norm_num) (by norm_num [Fin.sum_univ_two])

theorem centralState_matrix : centralState.matrix = (1/2:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  simp [centralState, diagonalState, Matrix.diagonal_apply, Matrix.one_apply]

theorem centralState_conjugated (U : unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    conjugatedState centralState U = centralState := by
  apply state_eq_of_matrix_eq
  change (U : Matrix (Fin 2) (Fin 2) ℂ) * centralState.matrix *
    (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = centralState.matrix
  rw [centralState_matrix]
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem U.property
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

def constantChannel (n m : ℕ) :
    QuantumChannel (Register (Fin n → Fin 2)) (Register (Fin m → Fin 2)) where
  toLinearMap := traceCLM.toLinearMap.smulRight (tensorState centralState m).1
  completelyPositive := fun _ _ hA => hA.replace _ (tensorState centralState m).2
  map_nonneg := by
    intro A hA
    change 0 ≤ traceCLM A • (tensorState centralState m).1.1
    rw [show traceCLM A = (‖A‖ : ℂ) from trace_eq_traceNorm_of_nonneg hA A.2]
    exact smul_nonneg (by exact_mod_cast norm_nonneg A) (tensorState centralState m).2
  trace_preserving := by
    intro A
    change traceCLM (traceCLM A • (tensorState centralState m).1) = traceCLM A
    rw [map_smul]
    have ht : traceCLM (tensorState centralState m).1 = 1 :=
      (Cloning.PhysicalCloningConverse.tensorDensity centralState m).trace_one
    rw [ht, smul_eq_mul, mul_one]

theorem constantChannel_output (n m : ℕ) (ρ : MatrixFidelity.State (Fin 2)) :
    (tensorState ρ n).map (constantChannel n m).toPositiveTracePreservingMap =
      tensorState centralState m := by
  apply Subtype.ext
  change traceCLM (tensorState ρ n).1 • (tensorState centralState m).1 = _
  have ht : traceCLM (tensorState ρ n).1 = 1 :=
    (Cloning.PhysicalCloningConverse.tensorDensity ρ n).trace_one
  rw [ht, one_smul]

/-- At the degeneracy itself the physical constant channel clones exactly,
at every finite pair of input and output sample sizes. -/
theorem constantChannel_central_payoff (n m : ℕ) :
    statePayoff n m (constantChannel n m) centralState = 1 := by
  rw [statePayoff, constantChannel_output, PositiveTraceClass.rootFidelity_self,
    norm_tensorState]

theorem constantChannel_payoff (n m : ℕ) (p : SimpleSpectrum 2)
    (U : unitary (Matrix (Fin 2) (Fin 2) ℂ)) :
    spectrumPayoff n m (constantChannel n m) p U =
      (tensorState centralState m).rootFidelity
        (tensorState (diagonalState p.eigenvalue (fun i => (p.positive i).le) p.normalized) m) := by
  let ρ := diagonalState p.eigenvalue (fun i => (p.positive i).le) p.normalized
  have hc : (tensorState centralState m).map
      (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap =
      tensorState centralState m := by
    apply Subtype.ext
    change (unitaryChannel (tensorUnitary U m)).toLinearMap (tensorState centralState m).1 = _
    rw [tensorState_conjugated, centralState_conjugated]
  have hp : (tensorState ρ m).map
      (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap =
      tensorState (conjugatedState ρ U) m := Subtype.ext (tensorState_conjugated ρ U m)
  change ((tensorState (orbitState p U) n).map _).rootFidelity _ = _
  rw [constantChannel_output]
  change (tensorState centralState m).rootFidelity (tensorState (conjugatedState ρ U) m) = _
  calc
    _ = ((tensorState centralState m).map
        (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap).rootFidelity
        ((tensorState ρ m).map
          (unitaryChannel (tensorUnitary U m)).toPositiveTracePreservingMap) := by rw [hc, hp]
    _ = _ := rootFidelity_unitaryChannel _ _ _

theorem tensor_diagonal_fidelity (m : ℕ) (p : SimpleSpectrum 2) :
    (tensorState centralState m).rootFidelity
      (tensorState (diagonalState p.eigenvalue (fun i => (p.positive i).le) p.normalized) m) =
    ∑ w : Fin m → Fin 2, Real.sqrt ((1/2:ℝ)^m * ∏ i, p.eigenvalue (w i)) := by
  rw [← Cloning.InfiniteFidelityHilbertSum.rootFidelity_matrixOf_basis
    (registerBasis (Fin m → Fin 2)).toOrthonormalBasis]
  simp only [HilbertBasis.coe_toOrthonormalBasis]
  change MatrixFidelity.fidelity
    (matrixOf (registerBasis _) (ofMatrix (registerBasis _) (tensorPower m centralState.matrix)))
    (matrixOf (registerBasis _) (ofMatrix (registerBasis _)
      (tensorPower m (Matrix.diagonal (fun i => (p.eigenvalue i : ℂ)))))) = _
  rw [matrixOf_ofMatrix (registerBasis _).orthonormal,
    matrixOf_ofMatrix (registerBasis _).orthonormal]
  change MatrixFidelity.fidelity
    (tensorPower m (Matrix.diagonal (fun _ => ((1/2:ℝ):ℂ))))
    (tensorPower m (Matrix.diagonal (fun i => (p.eigenvalue i : ℂ)))) = _
  rw [tensorPower_diagonal, tensorPower_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Complex.ofReal_pow,
    ← Complex.ofReal_prod]
  simpa only [BlockFidelity.classicalAffinity,
    Real.sqrt_mul (show 0 ≤ (1/2:ℝ)^m by positivity)] using
    MatrixFidelity.fidelity_diagonal_real (fun _ : Fin m → Fin 2 => (1/2:ℝ)^m)
    (fun w => ∏ i, p.eigenvalue (w i))
    (fun _ => pow_nonneg (by norm_num) _) (fun _ => Finset.prod_nonneg (fun _ _ => (p.positive _).le))

theorem diagonal_tensor_fidelity_tendsto {ι : Type*} {l : Filter ι}
    (p : ι → SimpleSpectrum 2)
    (hp : ∀ i, Tendsto (fun j => (p j).eigenvalue i) l (𝓝 (1/2:ℝ))) (m : ℕ) :
    Tendsto (fun j => (tensorState centralState m).rootFidelity
      (tensorState (diagonalState (p j).eigenvalue (fun i => ((p j).positive i).le)
        (p j).normalized) m)) l (𝓝 1) := by
  have h := tendsto_finset_sum Finset.univ (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Fin 2))) =>
    ((tendsto_finset_prod Finset.univ (fun i _ => hp (w i))).const_mul ((1/2:ℝ)^m)).sqrt)
  have hv : (∑ w : Fin m → Fin 2,
      Real.sqrt ((1/2:ℝ)^m * ∏ _i : Fin m, (1/2:ℝ))) = 1 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_two]
    rw [Real.sqrt_sq (by positivity : 0 ≤ (1/2:ℝ)^m)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  rw [hv] at h
  simpa only [tensor_diagonal_fidelity] using h

/-- A single physical constant channel approaches perfect fidelity uniformly
over all eigenbases when the qubit spectrum approaches degeneracy. -/
theorem constantChannel_uniform {ι : Type*} {l : Filter ι}
    (p : ι → SimpleSpectrum 2)
    (hp : ∀ i, Tendsto (fun j => (p j).eigenvalue i) l (𝓝 (1/2:ℝ)))
    (n m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ U : unitary (Matrix (Fin 2) (Fin 2) ℂ),
      1-ε < spectrumPayoff n m (constantChannel n m) (p j) U := by
  have h := (diagonal_tensor_fidelity_tendsto p hp m).eventually_const_lt
    (show 1-ε < 1 by linarith)
  filter_upwards [h] with j hj U
  rw [constantChannel_payoff]
  exact hj

/-- The physical all-channel optimum has the same fixed-sample degeneracy
limit, without restricting the channel optimization. -/
theorem fixed_samples_value_tendsto {ι : Type*} {l : Filter ι}
    (p : ι → SimpleSpectrum 2)
    (hp : ∀ i, Tendsto (fun j => (p j).eigenvalue i) l (𝓝 (1/2:ℝ))) (n m : ℕ) :
    Tendsto (fun j => knownSpectrumValue n m (p j)) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have h := constantChannel_uniform p hp n m (show 0 < 1-a by linarith)
    filter_upwards [h] with j hj
    have hb := LAN.candidate_le_minimaxValue (spectrumPayoff n m · (p j))
      (constantChannel n m) (spectrumPayoff n m (constantChannel n m) (p j) 1)
      (fun Φ U => spectrumPayoff_le_one n m Φ (p j) U)
      (fun U => by dsimp only; simp only [constantChannel_payoff, le_refl])
      (fun Φ U => spectrumPayoff_nonneg n m Φ (p j) U)
    change spectrumPayoff n m (constantChannel n m) (p j) 1 ≤ knownSpectrumValue n m (p j) at hb
    have hh := hj 1
    linarith
  · intro a ha
    exact Eventually.of_forall (fun j => (knownSpectrumValue_le_one n m (p j)).trans_lt ha)

theorem qubit_orbitalValue (p : SimpleSpectrum 2) (g : ℝ) :
    orbitalValue g p = Thermal.modeFactor g (p.eigenvalue 1/p.eigenvalue 0) := by
  have hi : (Finset.univ : Finset (PairIndex 2)) = {⟨(0,1),by decide⟩} := by decide
  simp only [orbitalValue, hi, Finset.prod_singleton, SimpleSpectrum.ratio]

theorem orbitalValue_degeneracy {ι : Type*} {l : Filter ι}
    (p : ι → SimpleSpectrum 2)
    (hp : ∀ i, Tendsto (fun j => (p j).eigenvalue i) l (𝓝 (1/2:ℝ)))
    {g : ℝ} (hg : 1 < g) :
    Tendsto (fun j => orbitalValue g (p j)) l (𝓝 (Thermal.classicalBase g)) := by
  have hr : Tendsto (fun j => (p j).eigenvalue 1/(p j).eigenvalue 0) l (𝓝 1) := by
    simpa using (hp 1).div (hp 0) (by norm_num : (1/2:ℝ) ≠ 0)
  have h := (Thermal.modeFactor_continuousAt (g := g) (q := 1) (by linarith)).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds hr)
  have he : Thermal.modeFactor g 1 = Thermal.classicalBase g := by
    simp only [Thermal.modeFactor, Thermal.classicalBase, one_mul, sub_add_cancel]
    ring
  simpa only [qubit_orbitalValue, Function.comp_apply, he] using h

/-- The two iterated limits are different for the genuine physical optimum:
taking the large-sample limit first gives a strict loss, while taking the
degeneracy limit first gives one at every sample size. -/
theorem noncommuting_limits (p : ℕ → SimpleSpectrum 2)
    (hp : ∀ i, Tendsto (fun j => (p j).eigenvalue i) atTop (𝓝 (1/2:ℝ)))
    (m : ℕ → ℕ) {g : ℝ} (hg : 1 < g)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 g)) :
    Tendsto (fun j => limsup (fun n => knownSpectrumValue n (m n) (p j)) atTop)
      atTop (𝓝 (Thermal.classicalBase g)) ∧
    Tendsto (fun n => limsup (fun j => knownSpectrumValue n (m n) (p j)) atTop)
      atTop (𝓝 1) ∧ Thermal.classicalBase g < 1 := by
  constructor
  · have he (j : ℕ) := (knownSpectrumValue_tendsto (p j) m g hg hgain).limsup_eq
    simpa only [he] using orbitalValue_degeneracy p hp hg
  constructor
  · have he (n : ℕ) := (fixed_samples_value_tendsto p hp n (m n)).limsup_eq
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  · exact Thermal.classicalBase_lt_one hg

/-- An explicit full-rank simple qubit spectrum with a vanishing gap. -/
def approachingSpectrum (j : ℕ) : SimpleSpectrum 2 where
  eigenvalue := ![(1+((j:ℝ)+3)⁻¹)/2, (1-((j:ℝ)+3)⁻¹)/2]
  positive := by
    have hj : 0 < (j:ℝ)+3 := by positivity
    have hi : ((j:ℝ)+3)⁻¹ < 1 := (inv_lt_one₀ hj).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    intro i
    fin_cases i
    · change 0 < (1+((j:ℝ)+3)⁻¹)/2
      positivity
    · change 0 < (1-((j:ℝ)+3)⁻¹)/2
      linarith
  strictAnti := by
    have hi : 0 < ((j:ℝ)+3)⁻¹ := by positivity
    intro i k hik
    have hi0 : i = 0 := by apply Fin.ext; have := k.isLt; change i.val < k.val at hik; omega
    have hk1 : k = 1 := by apply Fin.ext; have := k.isLt; change i.val < k.val at hik; omega
    subst i
    subst k
    change (1-((j:ℝ)+3)⁻¹)/2 < (1+((j:ℝ)+3)⁻¹)/2
    linarith
  normalized := by simp [Fin.sum_univ_two]; ring

theorem approachingSpectrum_tendsto (i : Fin 2) :
    Tendsto (fun j => (approachingSpectrum j).eigenvalue i) atTop (𝓝 (1/2:ℝ)) := by
  have h : Tendsto (fun j : ℕ => ((j:ℝ)+3)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop)
  fin_cases i
  · simpa [approachingSpectrum] using (h.const_add 1).div_const 2
  · simpa [approachingSpectrum] using (h.const_sub 1).div_const 2

/-- Concrete noncommutation: the spectrum path is constructed internally. -/
theorem concrete_noncommuting_limits (m : ℕ → ℕ) {g : ℝ} (hg : 1 < g)
    (hgain : Tendsto (fun n => (m n : ℝ)/n) atTop (𝓝 g)) :
    Tendsto (fun j => limsup (fun n => knownSpectrumValue n (m n) (approachingSpectrum j)) atTop)
      atTop (𝓝 (Thermal.classicalBase g)) ∧
    Tendsto (fun n => limsup (fun j => knownSpectrumValue n (m n) (approachingSpectrum j)) atTop)
      atTop (𝓝 1) ∧ Thermal.classicalBase g < 1 :=
  noncommuting_limits approachingSpectrum approachingSpectrum_tendsto m hg hgain

end Cloning.QubitDegeneracy
