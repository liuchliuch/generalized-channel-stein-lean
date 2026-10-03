import QuantumChannelStein.DivergenceOptimization

/-! # Canonical input marginals of coherently flagged finite permutation orbits -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.CovariantOrbitInput
open Matrix ChannelEntropy PureReferenceRecovery SpectralDecomposition
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {n : ℕ}

private theorem card_pos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩

def weight (G : Type*) [Fintype G] : ℝ := (Fintype.card G : ℝ)⁻¹

theorem weight_pos : 0 < weight G := inv_pos.mpr (Nat.cast_pos.mpr card_pos)

/-- The actual finite group average of a density matrix. -/
def averageDensity (p : G →* Equiv.Perm (Fin n)) (ω : State n) : State n where
  matrix := weight G • ∑ g : G, Matrix.reindex (p g) (p g) ω.matrix
  positive := by
    apply Matrix.PosSemidef.smul _ (weight_pos.le)
    apply Finset.sum_induction
    · intro A B hA hB
      exact hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro g _
      exact ω.positive.submatrix (p g).symm
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_sum]
    simp only [trace_reindex_equiv, ω.trace_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change (weight G : ℂ) * (Fintype.card G : ℂ) = 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    have hc : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt card_pos)
    simp only [weight, inv_mul_cancel₀ hc, Complex.ofReal_one]

/-- The finite group average is genuinely invariant under every represented permutation. -/
theorem averageDensity_invariant (p : G →* Equiv.Perm (Fin n)) (ω : State n) (h : G) :
    Matrix.reindex (p h) (p h) (averageDensity p ω).matrix = (averageDensity p ω).matrix := by
  have hs (g : G) (a : Fin n) : (p (h * g)).symm a = (p g).symm ((p h).symm a) := by
    rw [map_mul]
    rfl
  have hav : Matrix.reindex (p h) (p h) (averageDensity p ω).matrix =
      weight G • ∑ g : G, Matrix.reindex (p (h * g)) (p (h * g)) ω.matrix := by
    ext a b
    simp only [averageDensity, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Matrix.sum_apply, hs]
  rw [hav]
  change weight G • (∑ g : G, (fun k => Matrix.reindex (p k) (p k) ω.matrix) (h * g)) = _
  have hperm := Equiv.sum_comp (Equiv.mulLeft h)
    (fun k => Matrix.reindex (p k) (p k) ω.matrix)
  exact congrArg (fun X : Operator n => weight G • X) hperm

/-- Coefficients of the coherent orbit flag; the flag is retained in the reference. -/
def coefficient (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n) :
    Matrix (Fin (Fintype.card G * n)) (Fin n) ℂ := fun x a =>
  (Real.sqrt (weight G) : ℂ) * ψ.val ((finProdFinEquiv.symm x).2,
    (p ((Fintype.equivFin G).symm (finProdFinEquiv.symm x).1)).symm a)

@[simp] theorem coefficient_apply (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n)
    (g : G) (i a : Fin n) :
    coefficient p ψ (finProdFinEquiv ((Fintype.equivFin G) g,i)) a =
      (Real.sqrt (weight G) : ℂ) * ψ.val (i,(p g).symm a) := by
  change (Real.sqrt (weight G) : ℂ) * ψ.val ((finProdFinEquiv.symm
    (finProdFinEquiv ((Fintype.equivFin G) g,i))).2,
    (p ((Fintype.equivFin G).symm (finProdFinEquiv.symm
      (finProdFinEquiv ((Fintype.equivFin G) g,i))).1)).symm a) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The Gram matrix is exactly the averaged input density, including singular inputs. -/
theorem coefficient_gram (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n) :
    (coefficient p ψ)ᴴ * coefficient p ψ = (averageDensity p (inputDensity ψ)).matrix := by
  ext a b
  rw [Matrix.mul_apply]
  have hsum : (∑ x : Fin (Fintype.card G * n),
      star (coefficient p ψ x a) * coefficient p ψ x b) =
      ∑ g : G, ∑ i : Fin n,
        star (coefficient p ψ (finProdFinEquiv ((Fintype.equivFin G) g,i)) a) *
          coefficient p ψ (finProdFinEquiv ((Fintype.equivFin G) g,i)) b := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type,
      ← Equiv.sum_comp (Fintype.equivFin G)]
  change (∑ x, star (coefficient p ψ x a) * coefficient p ψ x b) = _
  rw [hsum]
  have hterm (g : G) (i : Fin n) :
      star (coefficient p ψ (finProdFinEquiv ((Fintype.equivFin G) g,i)) a) *
        coefficient p ψ (finProdFinEquiv ((Fintype.equivFin G) g,i)) b =
      (weight G : ℂ) * (star (ψ.val (i,(p g).symm a)) * ψ.val (i,(p g).symm b)) := by
    rw [coefficient_apply, coefficient_apply, StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]
    have hc : (Real.sqrt (weight G) : ℂ) * (Real.sqrt (weight G) : ℂ) = (weight G : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (weight_pos.le)]
    calc
      _ = ((Real.sqrt (weight G) : ℂ) * (Real.sqrt (weight G) : ℂ)) *
          (star (ψ.val (i,(p g).symm a)) * ψ.val (i,(p g).symm b)) := by simp only [Complex.star_def]; ring
      _ = _ := by simp only [hc, Complex.star_def]
  simp only [hterm, ← Finset.mul_sum]
  simp only [averageDensity, Matrix.smul_apply, Matrix.sum_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, inputDensity, coefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.real_smul, Complex.star_def]

/-- The coherent orbit input is a genuine unit vector with a finite larger reference. -/
def orbitInput (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n) :
    UnitPureInput (Fintype.card G * n) n :=
  ⟨WithLp.toLp 2 (fun q => coefficient p ψ q.1 q.2), by
    have hn : ‖WithLp.toLp 2 (fun q : Fin (Fintype.card G * n) × Fin n => coefficient p ψ q.1 q.2)‖ ^ 2 =
        ((coefficient p ψ)ᴴ * coefficient p ψ).trace.re := by
      rw [Matrix.trace_mul_comm]
      simp [EuclideanSpace.norm_sq_eq, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
    rw [coefficient_gram, (averageDensity p (inputDensity ψ)).trace_one, Complex.one_re] at hn
    nlinarith [norm_nonneg (WithLp.toLp 2
      (fun q : Fin (Fintype.card G * n) × Fin n => coefficient p ψ q.1 q.2))]⟩

theorem orbitInput_density (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n) :
    inputDensity (orbitInput p ψ) = averageDensity p (inputDensity ψ) := by
  apply state_eq_of_matrix_eq
  exact coefficient_gram p ψ

end QuantumChannelStein.CovariantOrbitInput
