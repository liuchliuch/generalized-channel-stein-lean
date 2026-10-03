import QuantumChannelStein.DivergenceOptimization
import QuantumChannelStein.StatePowerRenyi
import QuantumChannelStein.ChannelEntropyFiniteness

/-! # Literal trace-and-prepare channels and their Umegaki threshold

The map is `X ↦ trace X • rho`, realized by a normalized finite Kraus family
obtained from its proved positive Choi matrix. No replacer or tensor oracle
is used. All entropy statements retain the unsupported infinite case.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ReplacerChannel
open Matrix ChannelEntropy RelativeEntropy DivergenceOptimization
  PerfectDiscrimination StatePowerRenyi ChannelPowerReindex
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n m a b : ℕ}

def linearMap (n : ℕ) (ρ : State m) : MatrixMap n m where
  toFun X := X.trace • ρ.matrix
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.trace_smul, smul_smul]

theorem choi_linearMap (n : ℕ) (ρ : State m) :
    MatrixMap.choi (linearMap n ρ) = (1 : Operator n) ⊗ₖ ρ.matrix := by
  ext ⟨i,a⟩ ⟨j,b⟩
  by_cases h : i = j
  · subst j
    simp [MatrixMap.choi, linearMap, Matrix.trace, Matrix.diag, Matrix.single]
  · simp [MatrixMap.choi, linearMap, Matrix.trace, Matrix.diag, Matrix.single, h,
      show ∀ x, ¬ (i = x ∧ j = x) from fun x hx => h (hx.1.trans hx.2.symm)]

theorem linearMap_trace (n : ℕ) (ρ : State m) (X : Operator n) :
    ((linearMap n ρ) X).trace = X.trace := by
  simp [linearMap, Matrix.trace_smul, ρ.trace_one]

def channel (n : ℕ) (ρ : State m) : KrausChannel n m :=
  (MatrixMap.exists_kraus_of_choi_positive (linearMap n ρ)
    (by rw [choi_linearMap]; exact MatrixMap.posSemidef_kronecker Matrix.PosSemidef.one ρ.positive)
    (linearMap_trace n ρ)).choose

theorem channel_map (n : ℕ) (ρ : State m) : (channel n ρ).toLinearMap = linearMap n ρ :=
  (MatrixMap.exists_kraus_of_choi_positive (linearMap n ρ)
    (by rw [choi_linearMap]; exact MatrixMap.posSemidef_kronecker Matrix.PosSemidef.one ρ.positive)
    (linearMap_trace n ρ)).choose_spec.2

theorem channel_apply (n : ℕ) (ρ : State m) (X : Operator n) :
    (channel n ρ).apply X = X.trace • ρ.matrix :=
  congrArg (fun f : MatrixMap n m => f X) (channel_map n ρ)

@[simp] theorem channel_onState (n : ℕ) (ρ : State m) (τ : State n) :
    (channel n ρ).onState τ = ρ := by
  apply ChannelEntropy.state_eq_of_matrix_eq
  change (channel n ρ).apply τ.matrix = ρ.matrix
  rw [channel_apply, τ.trace_one, one_smul]

theorem channel_choi (n : ℕ) (ρ : State m) :
    (channel n ρ).choi = (1 : Operator n) ⊗ₖ ρ.matrix := by
  rw [← MatrixMap.choi_toLinearMap, channel_map, choi_linearMap]

theorem canonical_output (ρ : State m) (ω : State n) :
    pureOutput (channel n ρ) (TestingPrimal.densityInput ω) = ω.tensor ρ := by
  apply ChannelEntropy.state_eq_of_matrix_eq
  rw [canonical_output_matrix, channel_choi, State.tensor_matrix]
  congr 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  have hr : (CFC.sqrt ω.matrix)ᴴ = CFC.sqrt ω.matrix :=
    (CFC.sqrt_nonneg ω.matrix).posSemidef.isHermitian.eq
  rw [hr, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul,
    CFC.sqrt_mul_sqrt_self _ ω.positive.nonneg]

theorem channelD_eq (ρ σ : State m) (hn : 0 < n) :
    ChannelEntropy.channelD (channel n ρ) (channel n σ) = umegaki ρ σ := by
  have h := channelValue_eq_density_sup (fun ρ σ => umegaki ρ σ)
    (fun Φ ρ σ => umegaki_data_processing Φ ρ σ) (channel n ρ) (channel n σ)
  change ChannelEntropy.channelD (channel n ρ) (channel n σ) = _ at h
  rw [h]
  simp_rw [canonical_output, umegaki_tensor, umegaki_self, zero_add]
  letI : Nonempty (State n) := ⟨PureReferenceRecovery.inputDensity (unitProductInput hn)⟩
  simp

/-- Independent trace-and-prepare uses prepare the actual product density. -/
theorem tensor_map (ρ : State m) (τ : State b) :
    (KrausChannel.tensor (channel n ρ) (channel a τ)).toLinearMap =
      linearMap (n * a) (ρ.tensor τ) := by
  apply MatrixMap.choi_injective
  rw [MatrixMap.choi_toLinearMap, choi_linearMap]
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective j
  obtain ⟨⟨u,c⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := b)).surjective u
  obtain ⟨⟨v,d⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := b)).surjective v
  rw [choi_tensor_apply, channel_choi, channel_choi]
  simp [State.tensor_matrix, Matrix.reindex_apply, Matrix.one_apply,
    finProdFinEquiv.injective.eq_iff, Prod.mk.injEq, ite_and]
  split_ifs <;> simp_all

theorem tensor_map_of (Φ : KrausChannel n m) (Ψ : KrausChannel a b)
    (ρ : State m) (τ : State b) (hΦ : Φ.toLinearMap = linearMap n ρ)
    (hΨ : Ψ.toLinearMap = linearMap a τ) :
    (Φ.tensor Ψ).toLinearMap = linearMap (n*a) (ρ.tensor τ) := by
  rw [← MatrixMap.tensor_kraus_toLinearMap, hΦ, hΨ,
    ← channel_map n ρ, ← channel_map a τ, MatrixMap.tensor_kraus_toLinearMap]
  exact tensor_map ρ τ

theorem cast_map_of {n' m' : ℕ} (Φ : KrausChannel n m) (ρ : State m)
    (hΦ : Φ.toLinearMap = linearMap n ρ) (en : n = n') (em : m = m') :
    (Φ.cast en em).toLinearMap = linearMap n' (ρ.reindex (finCongr em)) := by
  cases en
  cases em
  have hs : ρ.reindex (finCongr rfl) = ρ := by
    apply ChannelEntropy.state_eq_of_matrix_eq
    ext i j
    rfl
  simpa [KrausChannel.cast, hs] using hΦ

/-- Every actual channel power is literally the trace-and-prepare map of
 the actual state power, including the zero-use unit. -/
theorem tensorPower_map (ρ : State m) (k : ℕ) :
    ((channel n ρ).tensorPower k).toLinearMap = linearMap (n^k) (statePower ρ k) := by
  induction k with
  | zero =>
    ext X i j
    simp [KrausChannel.tensorPower, KrausChannel.toLinearMap, KrausChannel.identity_apply,
      linearMap, statePower, TensorPower.tensorPower, Matrix.reindex_apply,
      Matrix.trace, Matrix.diag]
    letI : Subsingleton (Fin (n ^ 0)) := by rw [Nat.pow_zero]; infer_instance
    congr 1 <;> exact Subsingleton.elim _ _
  | succ k ih =>
    rw [KrausChannel.tensorPower, statePower_succ]
    exact cast_map_of _ _ (tensor_map_of _ _ _ _ (channel_map n ρ) ih) _ _

/-- Umegaki additivity for the independently repeated state matrices. -/
theorem umegaki_statePower (ρ σ : State m) (k : ℕ) :
    umegaki (statePower ρ k) (statePower σ k) = ((k : ℝ) : EReal) * umegaki ρ σ := by
  induction k with
  | zero => rw [statePower_zero_eq ρ σ, umegaki_self]; simp
  | succ k ih =>
    rw [statePower_succ, statePower_succ, umegaki_reindex, umegaki_tensor, ih]
    rw [Nat.cast_add, Nat.cast_one, EReal.coe_add, EReal.coe_one,
      EReal.right_distrib_of_nonneg (by exact_mod_cast (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) zero_le_one,
      one_mul, add_comm]

theorem channelD_tensorPower (ρ σ : State m) (hn : 0 < n) (k : ℕ) :
    ChannelEntropy.channelD ((channel n ρ).tensorPower k) ((channel n σ).tensorPower k) =
      ((k : ℝ) : EReal) * umegaki ρ σ := by
  rw [ChannelEntropy.channelD_congr _ (channel (n^k) (statePower ρ k))
    _ (channel (n^k) (statePower σ k))
    ((tensorPower_map ρ k).trans (channel_map _ _).symm)
    ((tensorPower_map σ k).trans (channel_map _ _).symm),
    channelD_eq _ _ (pow_pos hn k), umegaki_statePower]

/-- Replacer channels have exactly their state relative-entropy threshold,
including unsupported pairs with value infinity. -/
theorem regularizedD_eq (ρ σ : State m) (hn : 0 < n) :
    ChannelEntropy.regularizedD (channel n ρ) (channel n σ) = umegaki ρ σ := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    rw [channelD_tensorPower ρ σ hn k, ← mul_assoc, ← EReal.coe_mul,
      inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hk)), EReal.coe_one, one_mul]
  · rw [← channelD_eq ρ σ hn]
    exact channelD_le_regularizedD _ _

end QuantumChannelStein.ReplacerChannel
