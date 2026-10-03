import QuantumChannelStein.CovariantOrbitInput
import QuantumChannelStein.ChannelComposition

/-! # Actual controlled-output recovery from a coherent covariance flag -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.CovariantOrbitRecovery
open Matrix ChannelEntropy OperationalTesting MixedReferencePurification CovariantOrbitInput
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {n m : ℕ}

/-- Common finite permutation covariance of the actual channel action. -/
def Covariant (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ : KrausChannel n m) : Prop :=
  ∀ g : G, ∀ X : Operator n,
    Φ.apply (Matrix.reindex (p g) (p g) X) = Matrix.reindex (q g) (q g) (Φ.apply X)

def controlledInverse (q : G →* Equiv.Perm (Fin m)) :
    (Fin (Fintype.card G) × (Fin n × Fin m)) ≃ (Fin (Fintype.card G) × (Fin n × Fin m)) where
  toFun x := (x.1,(x.2.1,(q ((Fintype.equivFin G).symm x.1)).symm x.2.2))
  invFun x := (x.1,(x.2.1,(q ((Fintype.equivFin G).symm x.1)) x.2.2))
  left_inv := by rintro ⟨t,i,b⟩; simp
  right_inv := by rintro ⟨t,i,b⟩; simp

/-- Regroup the flag and undo the corresponding output permutation, without discarding coherence yet. -/
def recoveryEquiv (q : G →* Equiv.Perm (Fin m)) :
    Fin ((Fintype.card G * n) * m) ≃ Fin (Fintype.card G * (n * m)) :=
  finProdFinEquiv.symm.trans
    ((finProdFinEquiv.symm.prodCongr (Equiv.refl (Fin m))).trans
      ((Equiv.prodAssoc (Fin (Fintype.card G)) (Fin n) (Fin m)).trans
        ((controlledInverse q).trans
          (((Equiv.refl (Fin (Fintype.card G))).prodCongr finProdFinEquiv).trans finProdFinEquiv))))

@[simp] theorem recoveryEquiv_symm_apply (q : G →* Equiv.Perm (Fin m))
    (g : G) (i : Fin n) (b : Fin m) :
    (recoveryEquiv (n := n) q).symm (finProdFinEquiv ((Fintype.equivFin G) g,finProdFinEquiv (i,b))) =
      finProdFinEquiv (finProdFinEquiv ((Fintype.equivFin G) g,i),(q g) b) := by
  simp [recoveryEquiv, controlledInverse, Equiv.prodCongr_symm, Equiv.prodCongr_apply]

/-- First undo the controlled output permutation, then trace out the group flag. -/
def recoveryChannel (q : G →* Equiv.Perm (Fin m)) :
    KrausChannel ((Fintype.card G * n) * m) (n * m) :=
  (traceFirst (Fintype.card G) (n * m)).compose (KrausChannel.coordinateChange (recoveryEquiv q))

theorem traceFirst_apply (X : Operator (Fintype.card G * (n * m))) (i j : Fin (n * m)) :
    (traceFirst (Fintype.card G) (n * m)).apply X i j =
      ∑ t : Fin (Fintype.card G), X (finProdFinEquiv (t,i)) (finProdFinEquiv (t,j)) := by
  simp [traceFirst, KrausChannel.apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite]

theorem recoveryChannel_apply (q : G →* Equiv.Perm (Fin m))
    (X : Matrix (Fin (Fintype.card G * n) × Fin m) (Fin (Fintype.card G * n) × Fin m) ℂ)
    (i j : Fin n) (a b : Fin m) :
    (recoveryChannel q).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv X)
      (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      ∑ g : G, X (finProdFinEquiv ((Fintype.equivFin G) g,i),(q g) a)
        (finProdFinEquiv ((Fintype.equivFin G) g,j),(q g) b) := by
  rw [recoveryChannel, KrausChannel.compose_apply, KrausChannel.coordinateChange_apply, traceFirst_apply,
    ← Equiv.sum_comp (Fintype.equivFin G)]
  apply Finset.sum_congr rfl
  intro g _
  change X (finProdFinEquiv.symm ((recoveryEquiv q).symm
    (finProdFinEquiv ((Fintype.equivFin G) g,finProdFinEquiv (i,a)))))
    (finProdFinEquiv.symm ((recoveryEquiv q).symm
      (finProdFinEquiv ((Fintype.equivFin G) g,finProdFinEquiv (j,b))))) = _
  rw [recoveryEquiv_symm_apply, recoveryEquiv_symm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[simp] theorem orbitInput_apply (p : G →* Equiv.Perm (Fin n)) (ψ : UnitPureInput n n)
    (g : G) (i a : Fin n) :
    (orbitInput p ψ).val (finProdFinEquiv ((Fintype.equivFin G) g,i),a) =
      (Real.sqrt (weight G) : ℂ) * ψ.val (i,(p g).symm a) :=
  coefficient_apply p ψ g i a

/-- The diagonal flag blocks are exactly the permuted original output blocks. -/
theorem orbit_output_block (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ : KrausChannel n m) (hΦ : Covariant p q Φ) (ψ : UnitPureInput n n)
    (g : G) (i j : Fin n) (a b : Fin m) :
    Φ.amplify (Fintype.card G * n) (pureMatrix (orbitInput p ψ).val)
      (finProdFinEquiv ((Fintype.equivFin G) g,i),(q g) a)
      (finProdFinEquiv ((Fintype.equivFin G) g,j),(q g) b) =
      (weight G : ℂ) * Φ.amplify n (pureMatrix ψ.val) (i,a) (j,b) := by
  rw [KrausChannel.amplify_block]
  have hinput : (fun x y => pureMatrix (orbitInput p ψ).val
      (finProdFinEquiv ((Fintype.equivFin G) g,i),x)
      (finProdFinEquiv ((Fintype.equivFin G) g,j),y)) =
      (weight G : ℂ) • Matrix.reindex (p g) (p g) (fun x y => pureMatrix ψ.val (i,x) (j,y)) := by
    ext x y
    change (orbitInput p ψ).val (finProdFinEquiv ((Fintype.equivFin G) g,i),x) *
      star ((orbitInput p ψ).val (finProdFinEquiv ((Fintype.equivFin G) g,j),y)) =
      (weight G : ℂ) * (ψ.val (i,(p g).symm x) * star (ψ.val (j,(p g).symm y)))
    rw [orbitInput_apply, orbitInput_apply, StarMul.star_mul, Complex.star_def, Complex.conj_ofReal]
    have hc : (Real.sqrt (weight G) : ℂ) * (Real.sqrt (weight G) : ℂ) = (weight G : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt weight_pos.le]
    calc
      _ = ((Real.sqrt (weight G) : ℂ) * (Real.sqrt (weight G) : ℂ)) *
          (ψ.val (i,(p g).symm x) * star (ψ.val (j,(p g).symm y))) := by simp only [Complex.star_def]; ring
      _ = _ := by simp only [hc, Complex.star_def]
  rw [hinput, KrausChannel.apply_smul, hΦ g]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, KrausChannel.amplify_block]

theorem sum_weight (z : ℂ) : ∑ _g : G, (weight G : ℂ) * z = z := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  have hw : (Fintype.card G : ℂ) * (weight G : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    simp only [weight, mul_inv_cancel₀ hc, Complex.ofReal_one]
  rw [hw, one_mul]

/-- The same actual controlled channel recovers either original output hypothesis. -/
theorem recoveryChannel_pureOutput (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ : KrausChannel n m) (hΦ : Covariant p q Φ) (ψ : UnitPureInput n n) :
    (recoveryChannel q).onState (pureOutput Φ (orbitInput p ψ)) = pureOutput Φ ψ := by
  apply state_eq_of_matrix_eq
  ext i j
  obtain ⟨⟨i,a⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := m)).surjective i
  obtain ⟨⟨j,b⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := m)).surjective j
  change (recoveryChannel q).apply
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify _ (pureMatrix _)))
      (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) = _
  rw [recoveryChannel_apply]
  simp only [orbit_output_block p q Φ hΦ ψ, sum_weight]
  change _ = (Φ.amplify n (pureMatrix ψ.val))
    (finProdFinEquiv.symm (finProdFinEquiv (i,a)))
    (finProdFinEquiv.symm (finProdFinEquiv (j,b)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end QuantumChannelStein.CovariantOrbitRecovery
