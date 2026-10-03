import QuantumChannelStein.PureReferenceRecovery

/-! # Actual mixed-input purification and reference-only recovery channels -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.MixedReferencePurification
open Matrix ChannelEntropy OperationalTesting ChannelLocality
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {r n m e : ℕ}

/-- Trace out the first factor of a finite reference using explicit basis Kraus operators. -/
def traceFirst (e r : ℕ) : KrausChannel (e * r) r where
  rank := e
  kraus t i j := if finProdFinEquiv (t,i) = j then 1 else 0
  normalized := by
    ext i j
    obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv (m := e) (n := r)).surjective i
    obtain ⟨⟨c,d⟩,rfl⟩ := (finProdFinEquiv (m := e) (n := r)).surjective j
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      finProdFinEquiv.injective.eq_iff, Matrix.one_apply, Prod.mk.injEq, ite_and, apply_ite, eq_comm]
    split_ifs <;> simp_all

theorem traceFirst_tensor_apply (X : Matrix (Fin (e * r) × Fin n) (Fin (e * r) × Fin n) ℂ)
    (i j : Fin r) (a b : Fin n) :
    ((traceFirst e r).tensor (KrausChannel.identity n)).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv X)
      (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b)) =
      ∑ t : Fin e, X (finProdFinEquiv (t,i),a) (finProdFinEquiv (t,j),b) := by
  rw [tensor_apply_reindex]
  simp [Matrix.reindex_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, traceFirst, KrausChannel.identity,
    Matrix.one_apply, Equiv.symm_apply_apply, apply_ite]

/-- The square-root columns, grouped as a larger reference followed by the original input. -/
def purificationVector (ρ : State (r * n)) : EuclideanSpace ℂ (Fin ((r * n) * r) × Fin n) :=
  WithLp.toLp 2 (fun p => CFC.sqrt ρ.matrix
    (finProdFinEquiv ((finProdFinEquiv.symm p.1).2,p.2)) (finProdFinEquiv.symm p.1).1)

@[simp] theorem purificationVector_apply (ρ : State (r * n)) (t : Fin (r * n))
    (i : Fin r) (a : Fin n) :
    purificationVector ρ (finProdFinEquiv (t,i),a) = CFC.sqrt ρ.matrix (finProdFinEquiv (i,a)) t := by
  change CFC.sqrt ρ.matrix
    (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv (t,i))).2,a))
      (finProdFinEquiv.symm (finProdFinEquiv (t,i))).1 = _
  rw [Equiv.symm_apply_apply]

theorem purificationVector_recovered (ρ : State (r * n)) :
    ((traceFirst (r * n) r).tensor (KrausChannel.identity n)).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (pureMatrix (purificationVector ρ))) = ρ.matrix := by
  ext i j
  obtain ⟨⟨i,a⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := n)).surjective i
  obtain ⟨⟨j,b⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := n)).surjective j
  rw [traceFirst_tensor_apply]
  have hroot : (CFC.sqrt ρ.matrix).IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hgram : CFC.sqrt ρ.matrix * (CFC.sqrt ρ.matrix)ᴴ = ρ.matrix := by
    rw [hroot.eq]
    exact CFC.sqrt_mul_sqrt_self _ ρ.positive.nonneg
  have he := congrFun (congrFun hgram (finProdFinEquiv (i,a))) (finProdFinEquiv (j,b))
  change (∑ t, purificationVector ρ (finProdFinEquiv (t,i),a) *
    star (purificationVector ρ (finProdFinEquiv (t,j),b))) = _
  simp only [purificationVector_apply]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] using he

theorem purificationVector_norm (ρ : State (r * n)) : ‖purificationVector ρ‖ = 1 := by
  have h := congrArg Matrix.trace (purificationVector_recovered ρ)
  rw [KrausChannel.trace_apply, trace_reindex_equiv, ρ.trace_one] at h
  have hr := congrArg Complex.re h
  rw [trace_pureMatrix_re, Complex.one_re] at hr
  nlinarith [norm_nonneg (purificationVector ρ)]

def purificationInput (ρ : State (r * n)) : UnitPureInput ((r * n) * r) n :=
  ⟨purificationVector ρ, purificationVector_norm ρ⟩

/-- The constructed purification recovers exactly the original mixed state. -/
theorem purificationInput_recovered (ρ : State (r * n)) :
    ((traceFirst (r * n) r).tensor (KrausChannel.identity n)).onState
      (pureInputState (purificationInput ρ)) = ρ := by
  apply state_eq_of_matrix_eq
  exact purificationVector_recovered ρ

/-- Recovery remains reference-only after either arbitrary system channel. -/
theorem outputState_recovered (ρ : State (r * n)) (Φ : KrausChannel n m) :
    ((traceFirst (r * n) r).tensor (KrausChannel.identity m)).onState
      (pureOutput Φ (purificationInput ρ)) = outputState Φ r ρ := by
  have h := reference_recovery_output (traceFirst (r * n) r) Φ
    (pureInputState (purificationInput ρ))
  rw [purificationInput_recovered] at h
  have hp : outputState Φ ((r * n) * r) (pureInputState (purificationInput ρ)) =
      pureOutput Φ (purificationInput ρ) :=
    state_eq_of_matrix_eq _ _ (outputState_pureInputState_matrix Φ _)
  rwa [hp] at h

end QuantumChannelStein.MixedReferencePurification
