import QuantumChannelStein.ChannelEntropyChoi
import QuantumChannelStein.ChannelPowerReindex
import QuantumChannelStein.StateTensor
import QuantumChannelStein.RelativeEntropyReindex
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Concrete zero-type-II-error tests from failed support inclusion -/
noncomputable section
namespace QuantumChannelStein.PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix WithLp TensorPower ChannelPowerReindex

variable {d : ℕ}

/-- A safely normalized rank-one effect, defined for every vector. -/
def rankOneEffect (v : Fin d → ℂ) : Effect d := by
  let P : Operator d := Matrix.vecMulVec v (star v)
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  let t : ℝ := (1 + ‖P‖)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  refine ⟨t • P, hP.smul ht.le, ?_⟩
  letI : CStarAlgebra (Operator d) := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (t • P) (hP.smul ht.le).nonneg).mp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hden : 0 < 1 + ‖P‖ := by positivity
  change (1 + ‖P‖)⁻¹ * ‖P‖ ≤ 1
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_one hden).mpr (by linarith)

/-- The scale of the rank-one effect is strictly positive. -/
def rankOneScale (v : Fin d → ℂ) : ℝ :=
  (1 + ‖Matrix.vecMulVec v (star v)‖)⁻¹

@[simp] theorem rankOneEffect_matrix (v : Fin d → ℂ) :
    (rankOneEffect v).matrix = rankOneScale v • Matrix.vecMulVec v (star v) := rfl

theorem rankOneScale_pos (v : Fin d → ℂ) : 0 < rankOneScale v := by
  unfold rankOneScale
  positivity

/-- The actual Born probability is the scaled positive quadratic form. -/
theorem rankOneEffect_probability (v : Fin d → ℂ) (ρ : State d) :
    (rankOneEffect v).probability ρ = rankOneScale v * (star v ⬝ᵥ ρ.matrix *ᵥ v).re := by
  simp only [Effect.probability, rankOneEffect_matrix, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [dotProduct_mulVec, dotProduct_comm v]

/-- A state has strictly positive quadratic weight on every vector outside
its kernel. -/
theorem quadratic_pos_of_mulVec_ne_zero (ρ : State d) (v : Fin d → ℂ)
    (hv : ρ.matrix *ᵥ v ≠ 0) : 0 < (star v ⬝ᵥ ρ.matrix *ᵥ v).re := by
  have hnonneg := ρ.positive.dotProduct_mulVec_nonneg v
  have hre : 0 ≤ (star v ⬝ᵥ ρ.matrix *ᵥ v).re := (Complex.nonneg_iff.mp hnonneg).1
  apply lt_of_le_of_ne hre
  intro h
  apply hv
  apply (ρ.positive.dotProduct_mulVec_zero_iff v).mp
  apply Complex.ext
  · exact h.symm
  · exact (Complex.nonneg_iff.mp hnonneg).2.symm

/-- Failure of state support inclusion yields an actual nontrivial effect
whose alternative-state acceptance is exactly zero. -/
theorem exists_effect_of_not_supportIncluded (ρ σ : State d)
    (h : ¬ RelativeEntropy.supportIncluded ρ σ) :
    ∃ T : Effect d, 0 < T.probability ρ ∧ T.probability σ = 0 := by
  classical
  change ¬ ∀ v, v ∈ LinearMap.ker σ.matrix.mulVecLin →
    v ∈ LinearMap.ker ρ.matrix.mulVecLin at h
  push_neg at h
  obtain ⟨v, hvσ, hvρ⟩ := h
  change σ.matrix *ᵥ v = 0 at hvσ
  change ρ.matrix *ᵥ v ≠ 0 at hvρ
  refine ⟨rankOneEffect v, ?_, ?_⟩
  · rw [rankOneEffect_probability]
    exact mul_pos (rankOneScale_pos v) (quadratic_pos_of_mulVec_ne_zero ρ v hvρ)
  · rw [rankOneEffect_probability, hvσ]
    simp

/-- Choi support failure supplies an explicit one-use reference-assisted
test with positive null acceptance and zero alternative acceptance. -/
theorem exists_one_use_test {n m : ℕ} (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    ∃ T : Effect (n * m),
      0 < T.probability (ChannelEntropy.pureOutput Φ (ChannelEntropy.maximallyEntangledInput hn)) ∧
      T.probability (ChannelEntropy.pureOutput Ψ (ChannelEntropy.maximallyEntangledInput hn)) = 0 := by
  apply exists_effect_of_not_supportIncluded
  exact fun hs => h ((ChannelEntropy.normalizedChoi_support_iff Φ Ψ hn).mp hs)

end QuantumChannelStein.PerfectDiscrimination

noncomputable section
namespace QuantumChannelStein.PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix WithLp TensorPower ChannelPowerReindex

variable {d : ℕ}

/-- Tensor powers preserve positivity as actual Kronecker products. -/
theorem tensorPower_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (k : ℕ) :
    (TensorPower.tensorPower A k).PosSemidef := by
  induction k with
  | zero =>
    have heq : TensorPower.tensorPower A 0 = (1 : Matrix (Index ι 0) (Index ι 0) ℂ) := by
      simpa only [tensorPower_zero] using (tensorPower_one (m := ι) 0)
    rw [heq]
    exact Matrix.PosSemidef.one
  | succ k ih => exact MatrixMap.posSemidef_kronecker hA ih

/-- Traces of tensor powers are scalar powers of traces. -/
theorem trace_tensorPower {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (k : ℕ) :
    (TensorPower.tensorPower A k).trace = A.trace ^ k := by
  induction k with
  | zero => simp [tensorPower, Matrix.trace, Index]
  | succ k ih => rw [tensorPower_succ, Matrix.trace_kronecker, ih, pow_succ']

/-- Independent identical density matrices on canonically flattened coordinates. -/
def statePower (ρ : State d) (k : ℕ) : State (d ^ k) where
  matrix := Matrix.reindex (channelIndexEquiv d k) (channelIndexEquiv d k)
    (TensorPower.tensorPower ρ.matrix k)
  positive := (tensorPower_posSemidef ρ.matrix ρ.positive k).submatrix _
  trace_one := by
    rw [ChannelEntropy.trace_reindex_equiv, trace_tensorPower, ρ.trace_one, one_pow]

/-- Rejection is the complementary effect. -/
def complementEffect (T : Effect d) : Effect d where
  matrix := 1 - T.matrix
  positive := T.complement_positive
  complement_positive := by simpa using T.positive

@[simp] theorem complementEffect_probability (T : Effect d) (ρ : State d) :
    (complementEffect T).probability ρ = 1 - T.probability ρ := by
  simp [Effect.probability, complementEffect, Matrix.sub_mul, Matrix.trace_sub, ρ.trace_one]

/-- Tensor products of effects remain effects. -/
def effectPower (T : Effect d) (k : ℕ) : Effect (d ^ k) := by
  let P := Matrix.reindex (channelIndexEquiv d k) (channelIndexEquiv d k)
    (TensorPower.tensorPower T.matrix k)
  have hP : P.PosSemidef := (tensorPower_posSemidef T.matrix T.positive k).submatrix _
  refine ⟨P, hP, ?_⟩
  letI : CStarAlgebra (Operator (d ^ k)) := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg P hP.nonneg).mp
  change ‖Matrix.reindex _ _ (TensorPower.tensorPower T.matrix k)‖ ≤ 1
  rw [norm_reindex]
  exact norm_tensorPower_le_one T.matrix T.norm_matrix_le_one k

/-- The repeated OR test accepts if any single-copy detector accepts. -/
def repeatedEffect (T : Effect d) (k : ℕ) : Effect (d ^ k) :=
  complementEffect (effectPower (complementEffect T) k)

/-- Product effects on product states have exactly product probabilities. -/
theorem effectPower_probability (T : Effect d) (ρ : State d) (k : ℕ) :
    (effectPower T k).probability (statePower ρ k) = (T.probability ρ) ^ k := by
  unfold Effect.probability effectPower statePower
  change ((Matrix.reindexLinearEquiv ℂ ℂ (channelIndexEquiv d k) (channelIndexEquiv d k)
    (TensorPower.tensorPower T.matrix k)) *
    (Matrix.reindexLinearEquiv ℂ ℂ (channelIndexEquiv d k) (channelIndexEquiv d k)
      (TensorPower.tensorPower ρ.matrix k))).trace.re = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply,
    ChannelEntropy.trace_reindex_equiv, ← TensorPower.tensorPower_mul, trace_tensorPower]
  have hi : (T.matrix * ρ.matrix).trace.im = 0 :=
    (Complex.nonneg_iff.mp (trace_mul_nonnegative T.positive ρ.positive)).2.symm
  have hc : (T.matrix * ρ.matrix).trace = ((T.matrix * ρ.matrix).trace.re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [hc, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [Complex.ofReal_re]

/-- The repeated OR test has the exact success probability. -/
theorem repeatedEffect_probability (T : Effect d) (ρ : State d) (k : ℕ) :
    (repeatedEffect T k).probability (statePower ρ k) = 1 - (1 - T.probability ρ) ^ k := by
  rw [repeatedEffect, complementEffect_probability, effectPower_probability,
    complementEffect_probability]

end QuantumChannelStein.PerfectDiscrimination

noncomputable section
namespace QuantumChannelStein.PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix WithLp TensorPower ChannelPowerReindex

/-- Apply a coordinate equivalence independently to each tensor coordinate. -/
def indexMapEquiv {a b : Type*} (e : a ≃ b) (k : ℕ) : Index a k ≃ Index b k :=
  (indexEquiv a k).trans ((Equiv.piCongrRight (fun _ : Fin k => e)).trans
    (indexEquiv b k).symm)

@[simp] theorem indexEquiv_indexMapEquiv {a b : Type*} (e : a ≃ b) (k : ℕ)
    (i : Index a k) (l : Fin k) :
    indexEquiv b k (indexMapEquiv e k i) l = e (indexEquiv a k i l) := by
  simp [indexMapEquiv, Equiv.piCongrRight]

/-- Flatten the repeated one-use reference/output pairs. -/
def choiSourceEquiv (n m k : ℕ) : Index (Fin n × Fin m) k ≃ Fin ((n * m) ^ k) :=
  (indexMapEquiv finProdFinEquiv k).trans (channelIndexEquiv (n * m) k)

/-- Flatten reference and output groups for the actual repeated channel. -/
def choiTargetEquiv (n m k : ℕ) : Index (Fin n × Fin m) k ≃ Fin (n ^ k * m ^ k) :=
  (indexProdEquiv (Fin n) (Fin m) k).trans
    ((Equiv.prodCongr (channelIndexEquiv n k) (channelIndexEquiv m k)).trans finProdFinEquiv)

/-- The physical reference/output grouping permutation for repeated Choi states. -/
def choiStatePowerEquiv (n m k : ℕ) : Fin ((n * m) ^ k) ≃ Fin (n ^ k * m ^ k) :=
  (choiSourceEquiv n m k).symm.trans (choiTargetEquiv n m k)

@[simp] theorem choiTargetEquiv_apply (n m k : ℕ)
    (i : Index (Fin n) k) (a : Index (Fin m) k) :
    choiTargetEquiv n m k ((indexProdEquiv (Fin n) (Fin m) k).symm (i, a)) =
      finProdFinEquiv (channelIndexEquiv n k i, channelIndexEquiv m k a) := by
  simp [choiTargetEquiv, Equiv.prodCongr_apply]

@[simp] theorem choiStatePowerEquiv_symm_apply (n m k : ℕ)
    (i : Index (Fin n) k) (a : Index (Fin m) k) :
    (choiStatePowerEquiv n m k).symm
      (finProdFinEquiv (channelIndexEquiv n k i, channelIndexEquiv m k a)) =
        choiSourceEquiv n m k ((indexProdEquiv (Fin n) (Fin m) k).symm (i, a)) := by
  change choiSourceEquiv n m k ((choiTargetEquiv n m k).symm
    (finProdFinEquiv (channelIndexEquiv n k i, channelIndexEquiv m k a))) = _
  apply congrArg (choiSourceEquiv n m k)
  exact (choiTargetEquiv n m k).symm_apply_eq.mpr
    (choiTargetEquiv_apply n m k i a).symm

/-- The actual maximally entangled output of the repeated channel is the
repeated one-use Choi state, with the explicit physical grouping permutation. -/
theorem normalizedChoiState_power_matrix {n m : ℕ} (Φ : KrausChannel n m)
    (hn : 0 < n) (k : ℕ) :
    (ChannelEntropy.normalizedChoiState (KrausChannel.tensorPower Φ k) (pow_pos hn k)).matrix =
      Matrix.reindex (choiStatePowerEquiv n m k) (choiStatePowerEquiv n m k)
        (statePower (ChannelEntropy.normalizedChoiState Φ hn) k).matrix := by
  ext i j
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨i, rfl⟩ := (channelIndexEquiv n k).surjective i
  obtain ⟨j, rfl⟩ := (channelIndexEquiv n k).surjective j
  obtain ⟨a, rfl⟩ := (channelIndexEquiv m k).surjective a
  obtain ⟨b, rfl⟩ := (channelIndexEquiv m k).surjective b
  rw [ChannelEntropy.normalizedChoiState_matrix]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.smul_apply, choi_tensorPower_apply, choiStatePowerEquiv_symm_apply, statePower,
    choiSourceEquiv, Equiv.trans_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    tensorPower_apply_eq_prod, indexEquiv_indexMapEquiv, indexEquiv_indexProdEquiv_symm,
    ChannelEntropy.normalizedChoiState_matrix]
  simp only [Matrix.smul_apply, Complex.real_smul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
  simp only [← inv_pow, Complex.ofReal_pow]

/-- Reindex an actual effect by a finite coordinate permutation. -/
def reindexEffect {d d' : ℕ} (e : Fin d ≃ Fin d') (T : Effect d) : Effect d' := by
  let P := Matrix.reindex e e T.matrix
  have hP : P.PosSemidef := T.positive.submatrix _
  refine ⟨P, hP, ?_⟩
  letI : CStarAlgebra (Operator d') := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg P hP.nonneg).mp
  change ‖Matrix.reindex e e T.matrix‖ ≤ 1
  rw [norm_reindex]
  exact T.norm_matrix_le_one

/-- Relabeling both a test and a state preserves the actual Born probability. -/
theorem reindexEffect_probability {d d' : ℕ} (e : Fin d ≃ Fin d')
    (T : Effect d) (ρ : State d) :
    (reindexEffect e T).probability (ρ.reindex e) = T.probability ρ := by
  change ((Matrix.reindexLinearEquiv ℂ ℂ e e T.matrix) *
    (Matrix.reindexLinearEquiv ℂ ℂ e e ρ.matrix)).trace.re = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply,
    ChannelEntropy.trace_reindex_equiv]
  rfl

/-- Repeated OR detection on the actual reference/output space of k parallel uses. -/
def channelRepeatedEffect {n m : ℕ} (T : Effect (n * m)) (k : ℕ) :
    Effect (n ^ k * m ^ k) :=
  reindexEffect (choiStatePowerEquiv n m k) (repeatedEffect T k)

/-- Exact operational probability of the parallel repeated detector. -/
theorem channelRepeatedEffect_probability {n m : ℕ} (Φ : KrausChannel n m)
    (hn : 0 < n) (T : Effect (n * m)) (k : ℕ) :
    (channelRepeatedEffect T k).probability
      (ChannelEntropy.pureOutput (KrausChannel.tensorPower Φ k)
        (ChannelEntropy.maximallyEntangledInput (pow_pos hn k))) =
      1 - (1 - T.probability
        (ChannelEntropy.pureOutput Φ (ChannelEntropy.maximallyEntangledInput hn))) ^ k := by
  change ((channelRepeatedEffect T k).matrix *
    (ChannelEntropy.normalizedChoiState (KrausChannel.tensorPower Φ k) (pow_pos hn k)).matrix).trace.re = _
  rw [normalizedChoiState_power_matrix Φ hn k]
  change (reindexEffect (choiStatePowerEquiv n m k) (repeatedEffect T k)).probability
    ((statePower (ChannelEntropy.normalizedChoiState Φ hn) k).reindex
      (choiStatePowerEquiv n m k)) = _
  rw [reindexEffect_probability, repeatedEffect_probability]
  rfl

/-- Choi support failure yields actual parallel tests with exactly zero
alternative acceptance and exponentially convergent null acceptance. -/
theorem exists_parallel_zero_error_tests {n m : ℕ} (Φ Ψ : KrausChannel n m)
    (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      ∃ T : (k : ℕ) → Effect (n ^ k * m ^ k), ∀ k,
        (T k).probability (ChannelEntropy.pureOutput (KrausChannel.tensorPower Φ k)
          (ChannelEntropy.maximallyEntangledInput (pow_pos hn k))) = 1 - (1 - lam) ^ k ∧
        (T k).probability (ChannelEntropy.pureOutput (KrausChannel.tensorPower Ψ k)
          (ChannelEntropy.maximallyEntangledInput (pow_pos hn k))) = 0 := by
  obtain ⟨T, hpos, hzero⟩ := exists_one_use_test Φ Ψ hn h
  refine ⟨T.probability (ChannelEntropy.pureOutput Φ (ChannelEntropy.maximallyEntangledInput hn)),
    hpos, T.probability_le_one _, fun k => channelRepeatedEffect T k, ?_⟩
  intro k
  constructor
  · exact channelRepeatedEffect_probability Φ hn T k
  · rw [channelRepeatedEffect_probability Ψ hn T k, hzero]
    simp

/-- Eventually, the explicit parallel tests meet every positive type-I-error
tolerance while retaining exactly zero type-II error. -/
theorem eventually_exists_parallel_test {n m : ℕ} (Φ Ψ : KrausChannel n m)
    (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in Filter.atTop, ∃ T : Effect (n ^ k * m ^ k),
      1 - ε ≤ T.probability (ChannelEntropy.pureOutput (KrausChannel.tensorPower Φ k)
        (ChannelEntropy.maximallyEntangledInput (pow_pos hn k))) ∧
      T.probability (ChannelEntropy.pureOutput (KrausChannel.tensorPower Ψ k)
        (ChannelEntropy.maximallyEntangledInput (pow_pos hn k))) = 0 := by
  obtain ⟨lam, hlam, hlamone, T, hT⟩ := exists_parallel_zero_error_tests Φ Ψ hn h
  have hlim : Filter.Tendsto (fun k : ℕ => (1 - lam) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hlamone) (by linarith only [hlam])
  have hevent : ∀ᶠ k : ℕ in Filter.atTop, (1 - lam) ^ k < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hevent] with k hk
  refine ⟨T k, ?_, (hT k).2⟩
  rw [(hT k).1]
  linarith only [hk]

end QuantumChannelStein.PerfectDiscrimination
